#lang racket

(provide (all-defined-out))
(require racket/unsafe/ops
         web-server/private/util
         "../utils/main.rkt"
         "../ast/main.rkt"
         ;; For extra constants
         syntax/parse
         syntax/parse/define
         syntax/modresolve
         "expand.rkt"
         (prefix-in fake: "../fake-contract.rkt")
         "../primitives/main.rkt" ; for references to constants (e.g. `.null`)
         (for-syntax racket/base
                     racket/match
                     racket/list
                     racket/set
                     racket/syntax
                     syntax/parse
                     racket/contract
                     "../externals/for-parser.rkt"))

(define/contract (file->module p)
  (path-string? . -> . -module?)
  (port-count-lines-enabled #t)
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
     (define ℓ (syntax-ℓ prov))
     (define st-p (-struct/c 𝒾 st-doms ℓ))
     (define dec-constr
       (let* ([ℓₖ (ℓ-with-id ℓ  'constructor)]
              [ℓₑ (ℓ-with-id ℓₖ 'provide)])
         (-p/c-item (syntax-e #'s) (--> st-doms st-p ℓₖ) ℓₑ)))
     (define dec-pred
       (let* ([ℓₚ (ℓ-with-id ℓ  'predicate)]
              [ℓₑ (ℓ-with-id ℓₚ 'provide)])
         (-p/c-item (format-symbol "~a?" s-name)
                    (--> (list 'any/c) 'boolean? ℓₚ)
                    ℓₑ)))
     (define dec-acs
       (for/list ([ac (syntax->list #'(ac ...))]
                  [st-dom st-doms]
                  [i (in-naturals)])
         (define ℓᵢ (ℓ-with-id ℓ i))
         (define ℓₑ (ℓ-with-id ℓᵢ 'provide))
         (define ac-name (format-symbol "~a-~a" s-name (syntax-e ac)))
         (-p/c-item ac-name (--> (list st-p) st-dom ℓᵢ) ℓₑ)))
     (list* dec-constr dec-pred dec-acs)]
    [(#%plain-app (~literal list) x:id c:expr)
     (list (-p/c-item (syntax-e #'x) (parse-e #'c) (syntax-ℓ prov)))]))

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

    [(define-values (_ _ pred acc+muts ...)
       (let-values ([(_ ...)
                     (let-values ()
                       (let-values ()
                         (#%plain-app _ #;(~literal make-struct-type)
                                      (quote ctor-name)
                                      _
                                      (quote n:exact-integer)
                                      _ ...)))])
         (#%plain-app values _ _ _ mk-acc+muts ...)))
     (define ctor (syntax-e #'ctor-name))

     (define 𝒾 (-𝒾 ctor (cur-mod)))
     (define-values (accs muts)
       (let ([accs (make-hasheq)]
             [muts (make-hasheq)])
         (for ([name   (in-list (syntax->list #'(acc+muts ...)))]
               [clause (in-list (syntax->list #'(mk-acc+muts ...)))])
           (define/syntax-parse (#%plain-app mk _ (quote i:exact-integer) _) clause)
           (define m
             (syntax-parse #'mk
               [(~literal make-struct-field-accessor) accs]
               [(~literal make-struct-field-mutator ) muts]))
           (hash-set! m (syntax-e #'i) (syntax-e name)))
         (values accs muts)))
     
     (add-struct-info! 𝒾 (syntax-e #'n) (list->seteq (hash-keys muts)))
     (for ([name (in-sequences (list ctor (syntax-e #'pred))
                               (hash-values accs)
                               (hash-values muts))])
       (add-top-level! (-𝒾 name (cur-mod))))
     (let ([acc-list (hash->list accs)]
           [mut-list (hash->list muts)])
       (-define-values
        `(,ctor ,(syntax-e #'pred) ,@(map cdr acc-list) ,@(map cdr mut-list))
        (-@ 'values
            `(,(-st-mk 𝒾)
              ,(-st-p 𝒾)
              ,@(for/list ([i (in-list (map car acc-list))])
                  (-st-ac 𝒾 i))
              ,@(for/list ([i (in-list (map car mut-list))])
                  (-st-mut 𝒾 i)))
            (syntax-ℓ form))))]
    [(define-values (x:identifier) e) ; FIXME: separate case hack to "close" recursive contract
     (define lhs (syntax-e #'x))
     (define rhs (parse-e #'e))
     (define frees (free-x/c rhs))
     (cond
       [(set-empty? frees)
        (add-top-level! (-𝒾 lhs (cur-mod)))
        (-define-values (list lhs) rhs)]
       [(set-empty? (set-remove frees lhs))
        (define x (+x! 'rec))
        (add-top-level! (-𝒾 lhs (cur-mod)))
        (-define-values (list lhs)
           (-μ/c x (e/ (-x/c.tmp lhs) (-x/c x) rhs)))]
       [else
        (error 'TODO
               "In ~a's definition: arbitrary reference (recursive-contract ~a) not supported for now."
               lhs (set-first (set-remove frees lhs)))])]
    [(define-values (x:identifier ...) e)
     (define lhs (syntax->datum #'(x ...)))
     (for ([i lhs])
       (add-top-level! (-𝒾 i (cur-mod))))
     (-define-values lhs (parse-e #'e))]
    [(#%require spec ...)
     (-require (map parse-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes (k:id) ; constructor alias
       (#%plain-app
        (~literal make-self-ctor-checked-struct-info)
        _ _
        (#%plain-lambda () (quote-syntax k1:id))))
     (define lhs (syntax-e #'k1))
     (add-top-level! (-𝒾 lhs (cur-mod)))
     (-define-values (list lhs) (-𝒾 (syntax-e #'k) (cur-mod)))]
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
     (-list
      (for/list ([e (syntax->list #'(e ...))])
        (cons (syntax-ℓ e) (parse-e e))))]

    ;; HACK for immediate uses of accessors
    [(#%plain-app (~literal cadr) e)
     (match-define (list ℓ₁ ℓ₂) (ℓ-with-ids (syntax-ℓ stx) 2))
     (-@ -car (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)]
    [(#%plain-app (~literal caddr) e)
     (match-define (list ℓ₁ ℓ₂ ℓ₃) (ℓ-with-ids (syntax-ℓ stx) 3))
     (-@ -car (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)]

    ;; HACK for treating `apply` specially for precision.
    ;; This simply bypasses reading `apply` as wrapped reference to primitive
    [(#%plain-app f:id x ...)
     #:when #|HACK can't use ~literal for some reason|# (equal? 'apply (syntax-e #'f))
     (-@ 'apply (parse-es #'(x ...)) (syntax-ℓ stx))]

    ;; tmp HACK for varargs
    [(#%plain-app o e ...)
     #:when (syntax-parse #'o
              [(~or (~literal +) (~literal -) (~literal *) (~literal /)) #t]
              [_ #f])
     (define o-name (syntax-e #'o))
     (define ℓ (syntax-ℓ stx))
     (match (parse-es #'(e ...))
       [(list e) e]
       [(list e₁ e* ...)
        (for/fold ([e e₁]) ([eᵢ (in-list e*)] [i (in-naturals)])
          (-@ o-name (list e eᵢ) (ℓ-with-id ℓ i)))])]

    ;; HACKs for `variable-refererence-constant?`
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "call-with-output-file"))
     (-@ 'call-with-output-file  (parse-es #'(x ...)) (syntax-ℓ stx))]
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "call-with-input-file"))
     (-@ 'call-with-input-file (parse-es #'(x ...)) (syntax-ℓ stx))]
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "open-input-file"))
     (-@ 'open-input-file (parse-es #'(x ...)) (syntax-ℓ stx))]
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "open-output-file"))
     (-@ 'open-out-file (parse-es #'(x ...)) (syntax-ℓ stx))]
    [(if (#%plain-app (~literal variable-reference-constant?)
                      (#%variable-reference f:id))
         _
         (#%plain-app g:id x ...))
     #:when (and (free-identifier=? #'f #'g)
                 (string-prefix? (symbol->string (syntax-e #'f)) "file->list"))
     (-@ 'file->list (parse-es #'(x ...)) (syntax-ℓ stx))]
    

    ;;; Contracts
    ;; Non-dependent function contract
    [(let-values ([(_) (~literal fake:dynamic->*)]
                  [(_) (#%plain-app list c ...)]
                  [(_) (#%plain-app list d)])
       _ ...)
     (--> (parse-es #'(c ...)) (parse-e #'d) (syntax-ℓ stx))]
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
     (-->i cs mk-d (syntax-ℓ stx))]
    ;; independent varargs
    [(let-values ([(_) (~literal fake:dynamic->*)]
                  [(_) (#%plain-app list inits ...)]
                  [(_) rst]
                  [(_) rng])
       _ ...)
     (-->* (map parse-e (syntax->list #'(inits ...)))
           (parse-e #'rst)
           (parse-e #'rng)
           (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:listof) c)
     (-listof (parse-e #'c) (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:list/c) c ...)
     (define args
       (for/list ([cᵢ (in-list (syntax->list #'(c ...)))])
         (cons (syntax-ℓ cᵢ) (parse-e cᵢ))))
     (-list/c args)]
    [(#%plain-app (~literal fake:box/c) c)
     (-box/c (parse-e #'c) (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:vector/c) c ...)
     (-@ 'vector/c (parse-es #'(c ...)) (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:vectorof) c)
     (-@ 'vectorof (list (parse-e #'c)) (syntax-ℓ stx))]
    [(begin (#%plain-app (~literal fake:dynamic-struct/c) _ c ...)
            (#%plain-app _ _ _ _ (quote k) _ ...)
            _ ...)
     (define 𝒾 (-𝒾 (syntax-e #'k) (cur-mod)))
     (-struct/c 𝒾 (parse-es #'(c ...)) (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:=/c) c) (-comp/c '= (parse-e #'c))]
    [(#%plain-app (~literal fake:>/c) c) (-comp/c '> (parse-e #'c))]
    [(#%plain-app (~literal fake:>=/c) c) (-comp/c '>= (parse-e #'c))]
    [(#%plain-app (~literal fake:</c) c) (-comp/c '< (parse-e #'c))]
    [(#%plain-app (~literal fake:<=/c) c) (-comp/c '<= (parse-e #'c))]
    [(#%plain-app (~literal fake:cons/c) c d)
     (-cons/c (parse-e #'c) (parse-e #'d) (syntax-ℓ stx))]
    [(#%plain-app (~literal fake:one-of/c) c ...)
     (define args
       (for/list ([cᵢ (in-list (syntax->list #'(c ...)))])
         (cons (syntax-ℓ cᵢ) (parse-e cᵢ))))
     (-one-of/c args)]
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
         (syntax-ℓ stx))]
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
      (-begin/simp (parse-es #'(b ...)))
      (syntax-ℓ stx))]
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
      (-begin/simp (parse-es #'(b ...)))
      (syntax-ℓ stx))]
    [(quote e) (parse-quote #'e)]
    [(quote-syntax e) (error 'parse-e "TODO: (quote-syntax ~a)" (syntax->datum #'e))]
    [((~literal #%top) . id)
     (error "Unknown identifier ~a in module ~a" (syntax->datum #'id) (cur-mod))]
    [(#%variable-reference) (error 'parse-e "TODO: #%variable-reference")]
    [(#%variable-reference id)
     (match (symbol->string (syntax-e #'id)) ;; tmp HACK for slatex
       [(regexp #rx"^call-with-output-file")
        'call-with-output-file]
       [(regexp #rx"^call-with-input-file")
        'call-with-input-file]
       [_
        (error 'parse-e "TODO: #%variable-reference ~a, ~a" (syntax->datum #'id))])]

    ;; Hacks for now. Still need this because fake:any/c ≠ any/c
    ;[(~literal null) -null]
    ;[(~literal empty) -null]
    [(~literal fake:any/c) 'any/c]
    [(~literal fake:none/c) 'none/c]
    [(~literal fake:not/c) 'not/c]
    [(~literal fake:and/c) 'and/c]
    [(~literal fake:or/c ) 'or/c]
    
    ;; Hack for private identifiers
    [x:id #:when (equal? 'make-sequence (syntax-e #'x)) 'make-sequence]
    
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
         #:when (not (equal? src 'Λ))
         (-𝒾 (syntax-e #'i) src)]
        [_ (error 'parser "don't know what `~a` is" (syntax-e #'i))]))]))

(define/contract (parse-quote stx)
  (scv-syntax? . -> . -e?)
  (syntax-parse stx
    [(~or e:number e:str e:boolean e:id e:keyword e:char) (-b (syntax-e #'e))]
    [(l . r)
     (-@ -cons
         (list (parse-quote #'l) (parse-quote #'r))
         (syntax-ℓ stx))]
    [() -null]
    [#(x ...) (-@ 'vector (map parse-quote (syntax->list #'(x ...))) (syntax-ℓ stx))]
    [e (error 'parse-quote "unsupported quoted form: ~a" (syntax->datum #'e))]))

;; Parse given `formals` to extend environment
(define/contract (parse-formals formals)
  (scv-syntax? . -> . -formals?)
  (syntax-parse formals
    [(x:id ...) (syntax->datum #'(x ...))]
    [rest:id (-varargs '() (syntax-e #'rest))]
    [(x:id ... . rest:id) (-varargs (syntax->datum #'(x ...)) (syntax-e #'rest))]))

(define-for-syntax ext-names (get-defined-ext-names))
(define-for-syntax ext-name->stx get-ext-parse-result)

;; Return primitive with given `id`
(define/contract (parse-primitive id)
  (identifier?  . -> . (or/c #f -b? -o?))
  (log-debug "parse-primitive: ~a~n~n" (syntax->datum id))

  (define-syntax-parser make-parse-clauses
    [(_ id:id)
     #`(syntax-parse id
         #,@(for/list ([o (in-set ext-names)])
              #`[(~literal #,o) 
                 #,(match/values (ext-name->stx o)
                     [('quote name) #`(quote #,name)]
                     [('const name) (format-id #'id ".~a" name)]
                     [(_ _) (error 'make-parse-clause "~a" o)])])
         [_ #f])])

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
