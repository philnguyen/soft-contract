#lang racket
(require
 racket/unsafe/ops
 web-server/private/util
 "../utils/main.rkt" "../primitives/declarations.rkt" "../ast/main.rkt"
 ;; For extra constants
 racket/undefined racket/extflonum
 (only-in redex/reduction-semantics variable-not-in)
 syntax/parse syntax/modresolve
 "expand.rkt"
 (prefix-in fake: "../fake-contract.rkt")
 (for-syntax racket/base racket/match racket/list racket/set syntax/parse racket/contract
             "../primitives/declarations.rkt"))
(provide (all-defined-out))

(define/contract (file->module p)
  (path-string? . -> . -module?)
  (define p* (make-strawman p))
  (match-define (-module l body) (parse-top-level-form (do-expand-file p*)))
  (-module l (move-provides-to-end body)))

(define/contract cur-mod (parameter/c string? #|TODO|#)
  (make-parameter "top-level"))

(define scv-syntax? (and/c syntax? (not/c scv-ignore?)))

(define (mod-path->mod-name p)
  (match p ; hacks
    ['#%kernel 'Λ]
    ['#%unsafe 'unsafe]
    [(and (? symbol?) (app symbol->string "expanded module")) (cur-mod)]
    [_ (path->string (simplify-path p))]))

;; Convert syntax to `top-level-form`
(define/contract (parse-top-level-form form)
  (scv-syntax? . -> . -top-level-form?)
  (log-debug "parse-top-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path (#%plain-module-begin forms ...))
     (define mod-name (mod-path->mod-name (syntax-source #'id)))
     (-module
      mod-name
      (parameterize ([cur-mod mod-name])
        (filter
         values
         (for/list ([formᵢ (syntax->list #'(forms ...))]
                    #:when
                    (syntax-parse formᵢ
                      [((~literal module) (~literal configure-runtime) _ ...) #f]
                      [_ #t])
                    #:when
                    (scv-syntax? formᵢ))
           (parse-module-level-form formᵢ)))))]
    [((~literal begin) form ...)
     (-begin/simp (map parse-top-level-form (syntax->list #'(form ...))))]
    [((~literal #%expression) e) (parse-e #'e)]
    [_ (parse-general-top-level-form form)]))

;; Convert syntax to `module-level-form`. May fail for unsupported forms.
(define/contract (parse-module-level-form form)
  (scv-syntax? . -> . (or/c #f -module-level-form?))
  (log-debug "parse-module-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                call-with-values)
    [(#%provide spec ...)
     (error 'parse-module-level-form "Shouldn't reach here if using `fake-contract`")]
    [(#%declare _ ...) (error 'parse-module-level-form "TODO: '#%declare")]
    [(begin-for-syntax _ ...) #|ignore|# #f]
    
    ;; Hack for reading our fake-contracts:
    [(#%plain-app
      call-with-values
      (#%plain-lambda ()
        (#%plain-app (~literal fake:dynamic-provide/contract) prov ...))
      _)
     (-provide (append-map parse-provide-spec (syntax->list #'(prov ...))))]
    
    [_ (or (parse-general-top-level-form form)
           (parse-submodule-form form))]))

(define/contract (parse-provide-spec prov)
  (syntax? . -> . (listof -p/c-item?))
  (log-debug "parse-provide-spec:~n~a~n" (pretty (syntax->datum prov)))
  (syntax-parse prov #:literals (quote #%plain-app)
    [(#%plain-app (~literal fake:dynamic-struct-out)
                  (quote s:id)
                  (#%plain-app (~literal list) (quote ac:id) c) ...)
     (define cs (syntax->list #'(c ...)))
     (define n (length cs))
     (define s-name (syntax-e #'s))
     (define 𝒾 (-𝒾 s-name (cur-mod)))
     (define st-doms (map parse-e cs))
     (define st-p (-struct/c 𝒾 st-doms (+ℓ!)))
     (define dec-constr (-p/c-item (syntax-e #'s) (--> st-doms st-p (+ℓ!)) (+ℓ!)))
     (define dec-pred (-p/c-item (format-symbol "~a?" s-name) -pred (+ℓ!)))
     (define dec-acs
       (for/list ([ac (syntax->list #'(ac ...))]
                  [st-dom st-doms])
         (define ac-name (format-symbol "~a-~a" s-name (syntax-e ac)))
         (-p/c-item ac-name (--> (list st-p) st-dom (+ℓ!)) (+ℓ!))))
     (list* dec-constr dec-pred dec-acs)]
    [(#%plain-app (~literal list) x:id c:expr)
     (list (-p/c-item (syntax-e #'x) (parse-e #'c) (+ℓ!)))]))

(define/contract (parse-submodule-form form)
  (scv-syntax? . -> . (or/c #f -submodule-form?))
  (log-debug "parse-submodule-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path ((~literal #%plain-module-begin) d ...))
     (-module
      (path->string (simplify-path (syntax-source #'id)))
      (map parse-module-level-form (syntax->list #'(d ...))))]
    [((~literal module*) _ ...) (error 'parse-submodule-form "TODO: 'module*")]
    [_ #f]))

(define/contract (parse-general-top-level-form form)
  (scv-syntax? . -> . (or/c #f -general-top-level-form?))
  (log-debug "parse-general-top-level-form:~n~a~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (define-syntaxes define-values #%require let-values #%plain-app values
                call-with-values #%plain-lambda quote)
    ;; HACK against shits generated by recent versions of Racket (6.4+)
    ;; TODO: figure out proper way to handle this.
    [(define-values _ (#%plain-app do-partial-app _ ...))
     #:when (equal? 'do-partial-app (syntax->datum #'do-partial-app))
     #f]
    [(#%plain-app call-with-values (#%plain-lambda () e) print-values:id)
     #:when (equal? 'print-values (syntax->datum #'print-values))
     (parse-e #'e)]

    [(define-values (_ _ pred acc ...)
       (let-values ([(_ ...)
                     (let-values ()
                       (let-values ()
                         (#%plain-app _ (quote ctor-name) _ ...)))])
         (#%plain-app values _ _ _ (#%plain-app _ _ _ _) ...)))
     (log-debug "struct clause:~n~a~n" (pretty (syntax->datum form)))
     (define ctor (syntax-e #'ctor-name))
     (define/contract accs (listof identifier?) (syntax->list #'(acc ...)))
     (define n (length accs))
     (define 𝒾 (-𝒾 ctor (cur-mod)))
     (add-struct-info! 𝒾 n ∅eq)
     (-define-values
      (list* ctor (syntax-e #'pred) (map syntax-e accs))
      (-@ 'values
          (list* (-st-mk 𝒾)
                 (-st-p 𝒾)
                 (for/list ([(accᵢ i) (in-indexed accs)])
                   (-st-ac 𝒾 i)))
          0))]
    [(define-values (x:identifier) e) ; FIXME: separate case hack to "close" recursive contract
     (define lhs (syntax-e #'x))
     (define rhs (parse-e #'e))
     (define frees (free-x/c rhs))
     (cond
       [(set-empty? frees)
        (-define-values (list lhs) rhs)]
       [(set-empty? (set-remove frees lhs))
        (define pos (+ℓ!))
        (-define-values (list lhs)
           (-μ/c pos (e/ (-x/c.tmp lhs) (-x/c pos) rhs)))]
       [else
        (error 'TODO
               "In ~a's definition: arbitrary reference (recursive-contract ~a) not supported for now."
               lhs (set-first (set-remove frees lhs)))])]
    [(define-values (x:identifier ...) e)
     (-define-values (syntax->datum #'(x ...)) (parse-e #'e))]
    [(#%require spec ...)
     (-require (map parse-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes (k:id) ; constructor alias
       (#%plain-app
        (~literal make-self-ctor-checked-struct-info)
        _ _
        (#%plain-lambda () (quote-syntax k1:id))))
     (-define-values (list (syntax-e #'k1)) (-𝒾 (syntax-e #'k) (cur-mod)))]
    [(define-syntaxes _ ...) #f]
    [_ (parse-e form)]))

(define/contract (parse-e stx)
  (scv-syntax? . -> . -e?)
  (log-debug "parse-e: ~a~n~n" (pretty-format (syntax->datum stx)))

  (define/contract (parse-es es)
    ((and/c scv-syntax? (not/c identifier?)) . -> . (listof -e?))
    (map parse-e (syntax->list es)))

  (syntax-parse stx
    #:literals
    (let-values letrec-values begin begin0 if #%plain-lambda #%top
     module* module #%plain-app quote #%require quote-syntax
     with-continuation-mark #%declare #%provide case-lambda
     #%variable-reference set! list)

    ;; HACK for incomplete pattern matching error
    [(#%plain-app f _ ...)
     #:when (equal? 'match:error (syntax->datum #'f))
     (-error "incomplete pattern matching")]

    ;; HACK for time-apply in nucleic2
    [(let-values ([_ (#%plain-app (~literal time-apply) (#%plain-lambda () e) (~literal null))]) _ ...)
     (parse-e #'e)]

    ;; HACK for weird codegen
    [(let-values ([(v:id) (#%plain-lambda xs:id (#%plain-app _ u:id zs:id))])
       w:id)
     #:when (and (free-identifier=? #'v #'w)
                 (free-identifier=? #'xs #'zs))
     (parse-e #'u)]

    ;; HACK for `raise`-ing exception
    [(#%plain-app (~literal raise) _ ...)
     (-error "exception")]

    ;; HACK for immediate uses of `list`
    [(#%plain-app (~literal list) e ...)
     (-list (parse-es #'(e ...)))]

    ;; HACK for immediate uses of accessors
    [(#%plain-app (~literal cadr) e)
     (-@ (-𝒾 'car 'Λ)
         (list (-@ (-𝒾 'cdr 'Λ)
                   (list (parse-e #'e)) (+ℓ!))) (+ℓ!))]
    [(#%plain-app (~literal caddr) e)
     (-@ (-𝒾 'car 'Λ)
         (list (-@ (-𝒾 'cdr 'Λ)
                   (list (-@ (-𝒾 'cdr 'Λ)
                             (list (parse-e #'e)) (+ℓ!))) (+ℓ!))) (+ℓ!))]

    ;; HACK for treating `apply` specially for precision.
    ;; This simply bypasses reading `apply` as wrapped reference to primitive
    [(#%plain-app f:id x ...)
     #:when #|HACK can't use ~literal for some reason|# (equal? 'apply (syntax-e #'f))
     (-@ 'apply (parse-es #'(x ...)) (+ℓ!))]

    ;; tmp HACK for varargs
    [(#%plain-app o e ...)
     #:when (syntax-parse #'o
              [(~or (~literal +) (~literal -) (~literal *) (~literal /)) #t]
              [_ #f])
     (define o-name (syntax-e #'o))
     (match (parse-es #'(e ...))
       [(list e) e]
       [(list e₁ e* ...)
        (for/fold ([e e₁]) ([eᵢ e*])
          (-@ (-𝒾 o-name 'Λ) (list e eᵢ) (+ℓ!)))])]

    ;; HACKs for `variable-refererence-constant?`
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "call-with-output-file"))
     (-@ (-𝒾 'call-with-output-file 'Λ) (parse-es #'(x ...)) (+ℓ!))]
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "call-with-input-file"))
     (-@ (-𝒾 'call-with-input-file 'Λ) (parse-es #'(x ...)) (+ℓ!))]

    ;;; Contracts
    ;; Non-dependent function contract
    [(let-values ([(_) (~literal fake:dynamic->*)]
                  [(_) (#%plain-app list c ...)]
                  [(_) (#%plain-app list d)])
       _ ...)
     (--> (parse-es #'(c ...)) (parse-e #'d) (+ℓ!))]
    ;; Dependent contract
    [(~or (begin
            (#%plain-app
             (~literal fake:dynamic->i)
             (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
             (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
            _ ...)
          (let-values ()
            (#%plain-app
             (~literal fake:dynamic->i)
             (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
             (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
            _ ...)
          (#%plain-app
           (~literal fake:dynamic->i)
           (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
           (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...)))
     (define cs (parse-es #'(cₓ ...)))
     (define mk-d (-λ (syntax->datum #'(z ...)) (parse-e #'d)))
     (-->i cs mk-d (+ℓ!))]
    ;; independent varargs
    [(let-values ([(_) (~literal fake:dynamic->*)]
                  [(_) (#%plain-app list inits ...)]
                  [(_) rst]
                  [(_) rng])
       _ ...)
     (-->* (map parse-e (syntax->list #'(inits ...)))
           (parse-e #'rst)
           (parse-e #'rng))]
    [(#%plain-app (~literal fake:listof) c)
     (-listof (parse-e #'c))]
    [(#%plain-app (~literal fake:list/c) c ...)
     (-list/c (parse-es #'(c ...)))]
    [(#%plain-app (~literal fake:box/c) c)
     (-box/c (parse-e #'c))]
    [(#%plain-app (~literal fake:vector/c) c ...)
     (-@ (-𝒾 'vector/c 'Λ) (parse-es #'(c ...)) (+ℓ!))]
    [(#%plain-app (~literal fake:vectorof) c)
     (-@ (-𝒾 'vectorof 'Λ) (list (parse-e #'c)) (+ℓ!))]
    [(begin (#%plain-app (~literal fake:dynamic-struct/c) _ c ...)
            (#%plain-app _ _ _ _ (quote k) _ ...)
            _ ...)
     (define 𝒾 (-𝒾 (syntax-e #'k) (cur-mod)))
     (-struct/c 𝒾 (parse-es #'(c ...)) (+ℓ!))]
    [(#%plain-app (~literal fake:=/c) c) (-comp/c '= (parse-e #'c))]
    [(#%plain-app (~literal fake:>/c) c) (-comp/c '> (parse-e #'c))]
    [(#%plain-app (~literal fake:>=/c) c) (-comp/c '>= (parse-e #'c))]
    [(#%plain-app (~literal fake:</c) c) (-comp/c '< (parse-e #'c))]
    [(#%plain-app (~literal fake:<=/c) c) (-comp/c '<= (parse-e #'c))]
    [(#%plain-app (~literal fake:cons/c) c d)
     (-cons/c (parse-e #'c) (parse-e #'d))]
    [(#%plain-app (~literal fake:one-of/c) c ...)
     (-one-of/c (parse-es #'(c ...)))]
    [(~or (let-values ()
            (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...)
          (begin (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...))
     (-x/c.tmp (syntax-e #'x))]
    [(#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...)
     (-x/c.tmp (syntax-e #'x))]

    ;; Literals
    [(~or v:str v:number v:boolean) (-b (syntax->datum #'v))]
    ;; Ignore sub-modules
    [(module _ ...) (error 'parse-e "TODO: module")]
    [(module* _ ...) (error 'parse-e "TODO: module*")]
    [(#%declare _) (error 'parse-e "TODO: #%declare")]
    [_
     #:when (prefab-struct-key (syntax-e #'v))
     (error 'parse-e "TODO: non-top-level struct")]
    [(#%plain-app f x ...)
     (-@ (parse-e #'f)
         (parse-es #'(x ...))
         (+ℓ!))]
    [((~literal with-continuation-mark) e₀ e₁ e₂)
     (-wcm (parse-e #'e₀) (parse-e #'e₁) (parse-e #'e₂))]
    [(begin e ...) (-begin/simp (parse-es #'(e ...)))]
    [(begin0 e₀ e ...) (-begin0 (parse-e #'e₀) (parse-es #'(e ...)))]
    [(if i t e) (-if (parse-e #'i) (parse-e #'t) (parse-e #'e))]
    [(let-values () b ...) (-begin/simp (parse-es #'(b ...)))]
    [(let-values (bindings ...) b ...)
     (-let-values
      (for/list ([binding (syntax->list #'(bindings ...))])
        (syntax-parse binding
          [((x ...) e) (cons (syntax->datum #'(x ...)) (parse-e #'e))]))
      (-begin/simp (parse-es #'(b ...))))]
    [(set! i:identifier e)
     (define x
       (match (identifier-binding #'i)
         ['lexical (-x (syntax-e #'i))]
         [#f (-x (syntax-e #'i))]
         [(list (app (λ (x)
                       (parameterize ([current-directory (directory-part (cur-mod))])
                         ;(printf "part: ~a~n" (directory-part (cur-mod)))
                         ;(printf "id: ~a~n" #'i)
                         (mod-path->mod-name
                          (resolved-module-path-name (module-path-index-resolve x)))))
                     src)
                _ _ _ _ _ _)
          (-𝒾 (syntax-e #'i) src)]))
     (add-assignable! x)
     (-set! x (parse-e #'e))]
    [(#%plain-lambda fmls b ...+)
     (-λ (parse-formals #'fmls) (-begin/simp (parse-es #'(b ...))))]
    
    [(case-lambda [fml bodies ...+] ...)
     (-case-λ
      (for/list ([fmlᵢ (syntax->list #'(fml ...))]
                 [bodiesᵢ (syntax->list #'((bodies ...) ...))])
        ;; Compute case arity and extended context for RHS
        (cons (parse-formals fmlᵢ) (-begin/simp (parse-es bodiesᵢ)))))]
    [(letrec-values () b ...) (-begin/simp (parse-es #'(b ...)))]
    [(letrec-values (bindings ...) b ...)
     (-letrec-values
      (for/list ([bnd (syntax->list #'(bindings ...))])
        (syntax-parse bnd
          [((x ...) eₓ) (cons (syntax->datum #'(x ...)) (parse-e #'eₓ))]))
      (-begin/simp (parse-es #'(b ...))))]
    [(quote e) (parse-quote #'e)]
    [(quote-syntax e) (error 'parse-e "TODO: (quote-syntax ~a)" (syntax->datum #'e))]
    [((~literal #%top) . id)
     (error "Unknown identifier ~a in module ~a" (syntax->datum #'id) (cur-mod))]
    [(#%variable-reference) (error 'parse-e "TODO: #%variable-reference")]
    [(#%variable-reference id)
     (match (symbol->string (syntax-e #'id)) ;; tmp HACK for slatex
       [(regexp #rx"^call-with-output-file")
        (-𝒾 'call-with-output-file 'Λ)]
       [(regexp #rx"^call-with-input-file")
        (-𝒾 'call-with-input-file 'Λ)]
       [_
        (error 'parse-e "TODO: #%variable-reference ~a, ~a" (syntax->datum #'id))])]
    
    ;; Hacks for now. TODO: need this anymore??
    ;[(~literal null) -null]
    ;[(~literal empty) -null]
    [(~literal fake:any/c) (-𝒾 'any/c 'Λ)]
    [(~literal fake:none/c) (-𝒾 'none/c 'Λ)]
    [(~literal fake:not/c) (-𝒾 'not/c 'Λ)]
    [(~literal fake:and/c) (-𝒾 'and/c 'Λ)]
    [(~literal fake:or/c ) (-𝒾 'or/c  'Λ)]

    ;; Hack for private identifiers
    [x:id #:when (equal? 'make-sequence (syntax-e #'x)) (-𝒾 'make-sequence 'Λ)]
    
    [i:identifier
     (or
      (parse-primitive #'i)
      (match (identifier-binding #'i)
        ['lexical (-x (syntax-e #'i))]
        [#f (-x (syntax-e #'i))]
        [(list (app (λ (x)
                      (parameterize ([current-directory (directory-part (cur-mod))])
                        ;(printf "part: ~a~n" (directory-part (cur-mod)))
                        ;(printf "id: ~a~n" #'i)
                        (mod-path->mod-name
                         (resolved-module-path-name (module-path-index-resolve x)))))
                    src)
               _ _ _ _ _ _)
         (when (equal? 'not/c (syntax-e #'i))
           (error "done"))
         (-𝒾 (syntax-e #'i) src)]))]))

(define/contract (parse-quote stx)
  (scv-syntax? . -> . -e?)
  (syntax-parse stx
    [(~or e:number e:str e:boolean e:id e:keyword e:char) (-b (syntax-e #'e))]
    [(l . r)
     (-@ -cons
         (list (parse-quote #'l) (parse-quote #'r))
         (+ℓ!))]
    [() -null]
    [#(x ...) (-@ 'vector (map parse-quote (syntax->list #'(x ...))) (+ℓ!))]
    [e (error 'parse-quote "unsupported quoted form: ~a" (syntax->datum #'e))]))

;; Parse given `formals` to extend environment
(define/contract (parse-formals formals)
  (scv-syntax? . -> . -formals?)
  (syntax-parse formals
    [(x:id ...) (syntax->datum #'(x ...))]
    [rest:id (-varargs '() (syntax-e #'rest))]
    [(x:id ... . rest:id) (-varargs (syntax->datum #'(x ...)) (syntax-e #'rest))]))

;; Return primitive with given `id`
(define/contract (parse-primitive id)
  (identifier?  . -> . (or/c #f -𝒾? -b?))
  (log-debug "parse-primitive: ~a~n~n" (syntax->datum id))

  (define-syntax (make-parse-clauses stx)

    (syntax-parse stx
      [(_ id:id)
       ;; The reason we generate (syntax-parse) cases instead of set lookup
       ;; is to ensure that the source refers to the right reference

       (define/contract cache (hash/c symbol? any/c) (make-hasheq))

       (define/contract (make-clause dec)
         (any/c . -> . (listof syntax?))

         (define (make-ref s)
           (symbol? . -> . syntax?)
           #`(-𝒾 '#,s 'Λ))
         
         (match dec
           [`(#:pred ,s ,_ ...)
            (list #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [`(#:alias ,s ,t)
            (list #`[(~literal #,s)
                     #,(hash-ref! cache t (λ () (error 'make-ref "~a aliases undeclared ~a" s t)))])]
           [`(#:batch (,ss ...) ,(? arr?) ,_ ...)
            (for/list ([s ss])
              #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [`(,(? symbol? s) ,(? base? c))
            (list #`[(~literal #,s) #,(hash-ref! cache s #`(-b #,s))])]
           [(or `(,(? symbol? s) ,_ ...)
                `(#:struct-cons ,s ,_)
                `(#:struct-pred ,s ,_)
                `(#:struct-acc  ,s ,_ ,_)
                `(#:struct-mut  ,s ,_ ,_))
            (list #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [r
            (log-warning "unhandled in `make-parse-clauses` ~a~n" r)
            '()]))
       (define ans 
         #`(syntax-parse id
             #,@(append-map make-clause prims)
             [_ #f]))
       
       ;(printf "parse-primitive:~n~a~n" (syntax->datum ans))
       
       ans]))

  ;; Read off from primitive table
  (make-parse-clauses id))

(define/contract (parse-require-spec spec)
  (scv-syntax? . -> . -require-spec?)
  (syntax-parse spec
    [i:identifier (syntax-e #'i)]
    [_ (log-debug "parse-require-spec: ignore ~a~n" (syntax->datum spec)) 'dummy-require]))

;; Given path, insert fake-contract require and write to temp file
(define/contract (make-strawman p)
  (path-string? . -> . path-string?)
  (match (file->lines p)
    ;; If already required, leave alone (backward compatibility for existing tests)
    [(list _ ... l _ ...)
     #:when (regexp-match? #rx"(require soft-contract/fake-contract)" l)
     p]
    ;; Otherwise, assume expected format, then insert at 2 line
    [(list ls₀ ... (and l (regexp #rx"^#lang .+")) ls₁ ...)
     (define lines* `(,@ls₀ ,l "(require soft-contract/fake-contract)" ,@ls₁))
     (define p* (make-temporary-file "scv_strawman_~a.rkt"))
     (log-debug "Create strawman for `~a` at `~a`~n" p p*)
     (display-lines-to-file lines* p* #:exists 'replace)
     p*]
    [_
     (error "expect '~a' to be non-empty, with #lang declaration on 1 line" p)]))

(define/contract (move-provides-to-end forms)
  ((listof -module-level-form?) . -> . (listof -module-level-form?))
  (define-values (provides others)
    (for/fold ([provides '()] [others '()])
              ([form forms])
      (cond
        [(-provide? form) (values (cons form provides) others)]
        [else (values provides (cons form others))])))
  (append (reverse others) (reverse provides)))

;; For debugging only. Return scv-relevant s-expressions
(define/contract (scv-relevant path)
  (path-string? . -> . any/c)
  (for/list ([stxᵢ (syntax->list (do-expand-file path))]
             #:unless (scv-ignore? stxᵢ))
    (syntax->datum stxᵢ)))

