#lang racket

(provide parser-helper@)

(require (prefix-in c: racket/contract/base)
         racket/splicing
         set-extras
         racket/unit
         racket/unsafe/ops
         web-server/private/util
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         ;; For extra constants
         syntax/parse
         syntax/parse/define
         syntax/modresolve
         syntax/id-table
         "hacks.rkt"
         "expand.rkt"
         (prefix-in fake: "../fake-contract.rkt")
         "../signatures.rkt"
         "signatures.rkt"
         (for-syntax racket/base
                     racket/string
                     racket/match
                     racket/list
                     racket/set
                     racket/syntax
                     syntax/parse
                     racket/contract
                     ))

(define-unit parser-helper@
  (import static-info^ ast-macros^ meta-functions^ prims^)
  (export parser-helper^)
  (init-depend prims^)

  ;; Enable in "production" mode
  #;(define-syntax define/contract
      (syntax-parser
        [(_ x:id c e) #'(define x e)]
        [(_ lhs c rhs ...) #'(define lhs rhs ...)]))

  (define/contract struct-map (parameter/c (hash/c -𝒾? -𝒾?)) (make-parameter #f))
  (define/contract modules-to-parse (parameter/c (set/c (or/c symbol? string?))) (make-parameter #f))
  (define/contract id-occurence-count (parameter/c (hash/c symbol? integer?)) (make-parameter (make-hash)))
  (define/contract env (parameter/c immutable-free-id-table?) (make-parameter (make-immutable-free-id-table)))

  (define-syntax-rule (with-env ρ e ...) (parameterize ([env ρ]) e ...))

  (define/contract (inc-id! id)
    (identifier? . -> . symbol?)
    (define m (id-occurence-count))
    (define s (syntax-e id))
    (define old-count (hash-ref m s 0))
    (define name
      (case old-count
        [(0) s]
        [else (format-symbol "~a~a" s (n-sub old-count))]))
    (hash-set! m s (+ 1 old-count))
    name)

  (define (parse-files fns)
    ;((listof path-string?) . -> . (listof -module?))

    (parameterize ([port-count-lines-enabled #t]
                   [struct-map (make-hash)]
                   [modules-to-parse (list->set fns)]
                   [id-occurence-count (make-hasheq)])
      (define stxs (map do-expand-file fns))
      (for-each figure-out-aliases! stxs)

      (for-each figure-out-alternate-aliases!
                (parameterize ([expander expand])
                  (map do-expand-file fns)))
      
      (define ms (map parse-module stxs))

      ;; Re-order the modules for an appropriate initilization order,
      ;; learned from side-effects of `parse-module`
      (sort ms module-before? #:key -module-path)))

  (define/contract cur-mod (parameter/c string? #|TODO|#)
    (make-parameter "top-level"))

  (define scv-syntax? (and/c syntax? (not/c scv-ignore?)))

  (define (mod-path->mod-name p)
    (match p ; hacks
      ['#%kernel 'Λ]
      ['#%unsafe 'unsafe]
      [(and (? symbol?) (app symbol->string "expanded module")) (cur-mod)]
      [(or (? path-for-some-system?) (? path-string?)) (path->string (simplify-path p))]
      [(cons p _) (mod-path->mod-name p)]))

  (define/contract (figure-out-aliases! stx)
    (scv-syntax? . -> . void?)

    (define on-module-level-form!
      (syntax-parser
        #:literals (define-values #%plain-app quote)
        [(define-values (ex:id _) (#%plain-app do-partial-app _ _ (quote in:id) _ ...))
         #:when (equal? 'do-partial-app (syntax->datum #'do-partial-app)) ; TODO use "utils/evil"
         (define m (cur-mod))
         (define 𝒾ᵢₙ (-𝒾 (syntax-e #'in) m))
         (define 𝒾ₑₓ (-𝒾 (syntax-e #'ex) m))
         (set-export-alias! 𝒾ₑₓ 𝒾ᵢₙ)]
        [_ (void)]))
    
    (syntax-parse stx
      [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
       (parameterize ([cur-mod (mod-path->mod-name (syntax-source #'id))])
         (for-each on-module-level-form! (syntax->list #'(forms ...))))]
      [((~literal begin) form ...)
       (for-each figure-out-aliases! (syntax->list #'(form ...)))]
      [_ (void)]))

  (define/contract (figure-out-alternate-aliases! stx)
    (scv-syntax? . -> . void?)

    (define extractor->wrapper (make-hash))
    (define wrapper->name (make-hash))

    (define on-module-level-form!
      (syntax-parser
        #:literals (define-values #%plain-app quote)
        [(~and stx (define-values (wrapper:id _:id)
           (#%plain-app f _ _ (quote name:id) _ _)))
         #:when (eq? (syntax-e #'f) 'do-partial-app)
         (define m (cur-mod))
         (hash-set! wrapper->name (-𝒾 (syntax-e #'wrapper) m) (-𝒾 (syntax-e #'name) m))]
        [(define-values (extractor:id)
           (#%plain-app f wrapper:id))
         #:when (eq? (syntax-e #'f) 'wrapped-extra-arg-arrow-extra-neg-party-argument)
         (define m (cur-mod))
         (hash-set! extractor->wrapper (-𝒾 (syntax-e #'extractor) m) (-𝒾 (syntax-e #'wrapper) m))]
        [_ (void)]))

    (let go! ([stx stx])
      (syntax-parse stx
        [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
         (parameterize ([cur-mod (mod-path->mod-name (syntax-source #'id))])
           (for-each on-module-level-form! (syntax->list #'(forms ...))))]
        [((~literal begin) form ...)
         (for-each go! (syntax->list #'(form ...)))]
        [_ (void)]))

    (for ([(extractor wrapper) (in-hash extractor->wrapper)])
      (define orig (hash-ref wrapper->name wrapper))
      (set-alternate-alias! extractor orig #t)
      (set-alternate-alias! wrapper orig #f)))

  ;; Convert syntax to `top-level-form`
  (define/contract parse-top-level-form
    (scv-syntax? . -> . -top-level-form?)
    (syntax-parser
      #;[stx #:when (and (printf "top:~n~a~n" (pretty (syntax->datum #'stx)))
                         #f)
             (error "nah")]
      [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
       (define mod-name (mod-path->mod-name (syntax-source #'id)))

       (define care-about?
         (syntax-parser
           [((~literal module) (~literal configure-runtime) _ ...) #f]
           [form (scv-syntax? #'form)]))

       (-module
        mod-name
        (parameterize ([cur-mod mod-name])
          (define form-list ; Move "provide" clauses to the end
            (let-values ([(body provides)
                          (partition (syntax-parser
                                       [_:scv-provide #f]
                                       [_ #t])
                                     (syntax->list #'(forms ...)))])
              (append body provides)))
          (for*/list ([formᵢ (in-list form-list)] #:when (care-about? formᵢ)
                      [?res (in-value (parse-module-level-form formᵢ))] #:when ?res)
            ?res)))]
      [((~literal begin) form ...)
       (-begin/simp (map parse-top-level-form (syntax->list #'(form ...))))]
      [((~literal #%expression) e) (parse-e #'e)]
      [form (parse-general-top-level-form #'form)]))

  (define parse-module parse-top-level-form)

  ;; Convert syntax to `module-level-form`. May fail for unsupported forms.
  (define/contract parse-module-level-form
    (scv-syntax? . -> . (or/c #f -module-level-form?))
    (syntax-parser
      #:literals (#%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                            call-with-values)
      [(#%provide spec ...)
       (raise-syntax-error
        'parse-module-level-form
        "Shouldn't reach here if using `fake-contract`"
        #'(#%provide spec ...))]
      [(#%declare form ...)
       (raise-syntax-error 'parse-module-level-form "TODO: '#%declare" #'(#%declare form ...))]
      [(begin-for-syntax _ ...) #f]
      
      ;; Hack for reading our fake-contracts:
      [prov:scv-provide
       (-provide (append-map parse-provide-spec (syntax->list #'prov.provide-list)))]
      
      [form (or (parse-general-top-level-form #'form)
                (parse-submodule-form #'form))]))

  (define/contract parse-provide-spec
    (syntax? . -> . (listof -provide-spec?))
    (syntax-parser
      #:literals (quote #%plain-app)
      [(#%plain-app (~literal fake:dynamic-struct-out)
                    (quote s:id)
                    (#%plain-app (~literal list) (quote ac:id) c) ...)
       (define cs (syntax->list #'(c ...)))
       (define n (length cs))
       (define s-name (syntax-e #'s))
       (define 𝒾 (-𝒾 s-name (cur-mod)))
       (define st-doms (map parse-e cs))
       (define ℓ (syntax-ℓ #'s))
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
         (let ([offset (field-offset 𝒾)])
           (for/list ([ac (in-syntax-list #'(ac ...))]
                      [st-dom st-doms]
                      [i (in-naturals)] #:when (>= i offset))
             (define ℓᵢ (ℓ-with-id ℓ i))
             (define ℓₑ (ℓ-with-id ℓᵢ 'provide))
             (define ac-name (format-symbol "~a-~a" s-name (syntax-e ac)))
             (-p/c-item ac-name (--> (list st-p) st-dom ℓᵢ) ℓₑ))))
       (list* dec-constr dec-pred dec-acs)]
      [(#%plain-app (~literal list) x:id c:expr)
       (list (-p/c-item (syntax-e #'x) (parse-e #'c) (syntax-ℓ #'x)))]
      [x:id
       (list (syntax-e #'x))]))

  (define/contract parse-submodule-form
    (scv-syntax? . -> . (or/c #f -submodule-form?))
    (syntax-parser
      [((~or (~literal module) (~literal module*)) id path _)
       (printf "Warning: skip unsupported submodule `id`~n" (syntax-e #'id))
       #f]
      [_ #f]))

  (define/contract parse-general-top-level-form
    (scv-syntax? . -> . (or/c #f -general-top-level-form?))
    (syntax-parser
      #:literals (define-syntaxes define-values #%require let-values #%plain-app values
                   call-with-values #%plain-lambda quote list)
      [;; Handled by pass that figured-out aliases
       (define-values (ex:id _) (#%plain-app do-partial-app _ in:id _ ...))
       #:when (equal? 'do-partial-app (syntax->datum #'do-partial-app)) ; TODO use "utils/evil"
       #f]
      [;; Handled by pass that figured out alternate-aliases
       (define-values (lifted.0)
         (#%plain-app module-name-fixup
                      (#%plain-app variable-reference->module-source/submod (#%variable-reference))
                      (#%plain-app list)))
       #:when (and (eq? 'module-name-fixup (syntax-e #'module-name-fixup))
                   (eq? 'variable-reference->module-source/submod
                        (syntax-e #'variable-reference->module-source/submod)))
       (set-alternate-alias-id! (cur-mod) (syntax-e #'lifted.0))
       #f]
      [(#%plain-app call-with-values (#%plain-lambda () e) print-values:id)
       #:when (equal? 'print-values (syntax->datum #'print-values))
       (parse-e #'e)]

      [(~and stx (define-values (type:id _ pred acc+muts ...)
         (let-values ([(_ ...)
                       (let-values ()
                         (let-values ()
                           (#%plain-app (~literal make-struct-type)
                                        (quote ctor-name)
                                        parent
                                        (quote n:exact-integer)
                                        _ ...)))])
           (#%plain-app values _ _ _ mk-acc+muts ...))))
       
       (define ctor (syntax-e #'ctor-name))
       (define 𝒾 (-𝒾 ctor (cur-mod)))
       (hash-set! (struct-map) (id->𝒾 #'type) 𝒾)

       ;; Figure out parent struct
       (define ?parent
         (syntax-parse #'parent
           ['#f #f]
           [prnt:id (hash-ref (struct-map) (id->𝒾 #'prnt))]))
       (when ?parent
         (set-parent-struct! 𝒾 ?parent))
       (define offset (field-offset 𝒾))

       ;; Parse for direct field accessors/mutators
       (define-values (accs muts)
         (let ([accs (make-hasheq)]
               [muts (make-hasheq)])
           (for ([name   (in-syntax-list #'(acc+muts ...))]
                 [clause (in-syntax-list #'(mk-acc+muts ...))])
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
                    (-st-ac 𝒾 (+ offset i)))
                ,@(for/list ([i (in-list (map car mut-list))])
                    (-st-mut 𝒾 (+ offset i))))
              (syntax-ℓ #'pred))))]
      [;; Hack ignoring generated garbage by `struct`
       (define-values (_:identifier) (#%plain-app f:id _:id))
       #:when (equal? 'wrapped-extra-arg-arrow-extra-neg-party-argument (syntax-e #'f))
       #f]
      [(define-values (x:identifier) e) ; FIXME: separate case hack to "close" recursive contract
       (define lhs (syntax-e #'x))
       (define rhs (parse-e #'e))
       (define frees (free-x/c rhs))
       (cond
         [(set-empty? frees)
          (add-top-level! (-𝒾 lhs (cur-mod)))
          (-define-values (list lhs) rhs)]
         [(set-empty? (set-remove frees lhs))
          (define x (+x! (format-symbol "~a_~a" 'rec lhs)))
          (add-top-level! (-𝒾 lhs (cur-mod)))
          (-define-values (list lhs) (-μ/c x (e/ lhs (-x/c x) rhs)))]
         [else
          (raise-syntax-error
           'recursive-contract
           "arbitrary recursive contract reference not supported for now."
           #'(define-values (x) e)
           #'e)])]
      [(define-values (x:identifier ...) e)
       (define lhs (syntax->datum #'(x ...)))
       (for ([i lhs])
         (add-top-level! (-𝒾 i (cur-mod))))
       (-define-values lhs (parse-e #'e))]
      [(#%require spec ...)
       (-require (map parse-require-spec (syntax->list #'(spec ...))))]
      [(define-syntaxes (k:id) ; constructor alias
         (~and rhs
               (#%plain-app
                (~literal make-self-ctor-checked-struct-info)
                _ _
                (#%plain-lambda () (quote-syntax k1:id)))))
       (define lhs (syntax-e #'k1))
       (add-top-level! (-𝒾 lhs (cur-mod)))
       (-define-values (list lhs) (-x (-𝒾 (syntax-e #'k) (cur-mod)) (syntax-ℓ #'rhs)))]
      [(define-syntaxes _ ...) #f]
      [form (parse-e #'form)]))

  (define/contract (parse-es es)
    ((and/c scv-syntax? (not/c identifier?)) . -> . (listof -e?))
    (map parse-e (syntax->list es)))

  (define (parse-e stx)
    ;(scv-syntax? . -> . -e?)
    (log-debug "parse-e: ~a~n~n" (pretty-format (syntax->datum stx)))

    (syntax-parse stx
      #:literals
      (let-values letrec-values begin begin0 if #%plain-lambda #%top
                  module* module #%plain-app quote #%require quote-syntax
                  with-continuation-mark #%declare #%provide case-lambda
                  #%variable-reference set! list)

      ;; HACK for incomplete pattern matching error
      [(#%plain-app f _ ...)
       #:when (equal? 'match:error (syntax->datum #'f))
       (-error "incomplete pattern matching" (syntax-ℓ stx))]

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
       (-@ 'raise #|TODO|# '() (syntax-ℓ stx))]

      ;; HACK for immediate uses of `list`
      [(#%plain-app (~literal list) e ...)
       (-list
        (for/list ([e (in-syntax-list #'(e ...))])
          (cons (syntax-ℓ e) (parse-e e))))]

      ;; HACK for immediate uses of accessors
      [(#%plain-app (~literal cadr) e)
       (match-define (list ℓ₁ ℓ₂) (ℓ-with-ids (syntax-ℓ stx) 2))
       (-@ -car (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)]
      [(#%plain-app (~literal caddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃) (ℓ-with-ids (syntax-ℓ stx) 3))
       (-@ -car (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)]
      [(#%plain-app (~literal cadddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃ ℓ₄) (ℓ-with-ids (syntax-ℓ stx) 4))
       (-@ -car (list (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)) ℓ₄)]
      [(#%plain-app (~literal cddddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃ ℓ₄) (ℓ-with-ids (syntax-ℓ stx) 4))
       (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)) ℓ₄)]

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
       (define o.name (syntax-e #'o))
       (define ℓ (syntax-ℓ stx))
       (match (parse-es #'(e ...))
         [(list e) e]
         [(list e₁ e* ...)
          (for/fold ([e e₁]) ([eᵢ (in-list e*)] [i (in-naturals)])
            (-@ o.name (list e eᵢ) (ℓ-with-id ℓ i)))])]

      ;; HACKs for `variable-refererence-constant?`
      [app:indirect-app
       (-@ (attribute app.fun-name) (parse-es #'app.args) (syntax-ℓ #'app))]

      ;; HACK for figuring out exports from non-faked files
      [(#%plain-app f:id lifted.0 args ...)
       #:when (equal? (syntax-e #'lifted.0) (get-alternate-alias-id (cur-mod) (λ () #f)))
       (define f.src (id-defining-module #'f))
       (match-define (cons f-resolved wrap?)
         (get-alternate-alias
          (-𝒾 (syntax-e #'f) f.src)
          (λ () (raise (exn:missing "missing" (current-continuation-marks) f.src (syntax-e #'f))))))
       (set-module-before! f.src (cur-mod))
       (define f-ref (-x f-resolved (syntax-ℓ #'f)))
       (cond
         [wrap? (-@ f-ref (parse-es #'(args ...)) (syntax-ℓ stx))]
         [(and (not wrap?) (null? (syntax->list #'(args ...)))) f-ref]
         [else (error 'parser "my understanding is wrong")])]
      

    ;;; Contracts
      ;; Non-dependent function contract
      [(let-values ([(_) (~literal fake:dynamic->*)]
                    [(_) (#%plain-app list c ...)]
                    [(_) rng])
         _ ...)
       (syntax-parse #'rng
         [(#%plain-app list d) (--> (parse-es #'(c ...)) (parse-e #'d) (syntax-ℓ stx))]
         [_                    (--> (parse-es #'(c ...)) 'any (syntax-ℓ stx))])]
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
       (define mk-d
         (let-values ([(xs ρ) (parse-formals #'(z ...))])
           (-λ xs (with-env ρ (parse-e #'d)))))
       (-->i cs mk-d (syntax-ℓ stx))]
      ;; independent varargs
      [(let-values ([(_) (~literal fake:dynamic->*)]
                    [(_) (#%plain-app list inits ...)]
                    [(_) rst]
                    [(_) rng])
         _ ...)
       (syntax-parse #'rng
         [(#%plain-app list d)
          (--> (-var (parse-es #'(inits ...)) (parse-e #'rst))
               (parse-e #'d)
               (syntax-ℓ stx))]
         [_
          (--> (-var (parse-es #'(inits ...)) (parse-e #'rst))
               'any
               (syntax-ℓ stx))])]
      [(#%plain-app (~literal fake:list/c) c ...)
       (define args
         (for/list ([cᵢ (in-syntax-list #'(c ...))])
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
      [(#%plain-app (~literal fake:=/c) c) (-comp/c '= (parse-e #'c) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:>/c) c) (-comp/c '> (parse-e #'c) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:>=/c) c) (-comp/c '>= (parse-e #'c) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:</c) c) (-comp/c '< (parse-e #'c) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:<=/c) c) (-comp/c '<= (parse-e #'c) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:cons/c) c d)
       (-cons/c (parse-e #'c) (parse-e #'d) (syntax-ℓ stx))]
      [(#%plain-app (~literal fake:one-of/c) c ...)
       (-@ 'one-of/c (parse-es #'(c ...)) (syntax-ℓ stx))]
      [(~or (let-values ()
              (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)) _ ...)
            (begin (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)) _ ...)
            (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)))
       (syntax-parse #'t
         [((~or #:chaperone #:flat))
          (-x/c.tmp (syntax-e #'x))]
         [_
          (raise-syntax-error 'recursive-contract "must be #:chaperone or #:flat" #'t)])]

      ;; Literals
      [(~or v:str v:number v:boolean) (-b (syntax->datum #'v))]
      ;; Ignore sub-modules
      [(module _ ...) (raise-syntax-error 'parse-e "TODO: module" stx)]
      [(module* _ ...) (raise-syntax-error 'parse-e "TODO: module*" stx)]
      [(#%declare _) (raise-syntax-error 'parse-e "TODO: #%declare" stx)]
      [stx
       #:when (prefab-struct-key (syntax-e #'v))
       (raise-syntax-error 'parse-e "TODO: non-top-level struct" #'stx)]
      [(#%plain-app f x ...)
       (-@/simp (parse-e #'f) (parse-es #'(x ...)) (syntax-ℓ stx))]
      [(with-continuation-mark e₀ e₁ e₂)
       (-wcm (parse-e #'e₀) (parse-e #'e₁) (parse-e #'e₂))]
      [(begin e ...)
       (syntax-parse #'(e ...)
         #:literals (with-continuation-mark #%plain-app #%variable-reference let-values)
         [;; Hack for requiring wrapped stuff
          ((with-continuation-mark
             (~literal c:contract-continuation-mark-key)
             _
             (let-values ()
               (#%plain-app id0:id
                            (#%plain-app module-name-fixup
                                         (#%plain-app variable-reference->module-source/submod
                                                      (#%variable-reference))
                                         (#%plain-app list))))))
          (define src (id-defining-module #'id0))
          (define 𝒾ₑₓ (-𝒾 (syntax-e #'id0) src))
          (set-module-before! src (cur-mod))
          (-x (get-export-alias 𝒾ₑₓ (λ () (raise (exn:missing "missing" (current-continuation-marks) src (syntax-e #'id0))))) (syntax-ℓ stx))]
         [_
          (-begin/simp (parse-es #'(e ...)))])]
      [(begin0 e₀ e ...) (-begin0 (parse-e #'e₀) (parse-es #'(e ...)))]
      [(if i t e)
       (-if/simp (parse-e #'i) (parse-e #'t) (parse-e #'e))]
      [(let-values (bindings ...) b ...)
       (define-values (bindings-rev ρ)
         (for/fold ([bindings-rev '()] [ρ (env)])
                   ([bnd (in-syntax-list #'(bindings ...))])
           (syntax-parse bnd
             [((x ...) e)
              (define-values (xs ρ*) (parse-formals #'(x ...) #:base ρ))
              (values (cons (cons xs (parse-e #'e)) bindings-rev) ρ*)])))
       (-let-values/simp (reverse bindings-rev)
                         (with-env ρ (-begin/simp (parse-es #'(b ...))))
                         (syntax-ℓ stx))]
      [(set! i:identifier e)
       (match-define (-x x _) (parse-ref #'i))
       (set-assignable! x)
       (-set! x (parse-e #'e))]
      [(#%plain-lambda fmls b ...+)
       (define-values (xs ρ) (parse-formals #'fmls))
       (-λ xs (with-env ρ (-begin/simp (parse-es #'(b ...)))))]
      
      [(case-lambda [fml bodies ...+] ...)
       (-case-λ
        (for/list ([fmlᵢ (in-syntax-list #'(fml ...))]
                   [bodiesᵢ (in-syntax-list #'((bodies ...) ...))])
          ;; Compute case arity and extended context for RHS
          (define-values (xsᵢ ρᵢ) (parse-formals fmlᵢ))
          (cons xsᵢ (with-env ρᵢ (-begin/simp (parse-es bodiesᵢ))))))]
      [(letrec-values () b ...) (-begin/simp (parse-es #'(b ...)))]
      [(letrec-values (bindings ...) b ...)
       (define-values (lhss-rev ρ)
         (for/fold ([lhss-rev '()] [ρ (env)])
                   ([bnd (in-syntax-list #'(bindings ...))])
           (syntax-parse bnd
             [((x ...) _)
              (define-values (lhs ρ*) (parse-formals #'(x ...) #:base ρ))
              (values (cons lhs lhss-rev) ρ*)])))
       (-letrec-values
        (for/list ([lhs (in-list (reverse lhss-rev))]
                   [bnd (in-syntax-list #'(bindings ...))])
          (syntax-parse bnd
            [(_ eₓ) (cons lhs (with-env ρ (parse-e #'eₓ)))]))
        (with-env ρ (-begin/simp (parse-es #'(b ...))))
        (syntax-ℓ stx))]
      [(quote e) (parse-quote #'e)]
      [(quote-syntax e)
       (raise-syntax-error 'parse-e "TODO: ~a" stx)]
      [((~literal #%top) . id)
       (raise-syntax-error 'parse-e "Unknown identifier" stx #'id)]
      [(#%variable-reference)
       (raise-syntax-error 'parse-e "TODO:" stx)]
      [(#%variable-reference id)
       (match (symbol->string (syntax-e #'id)) ;; tmp HACK for slatex
         [(regexp #rx"^call-with-output-file")
          'call-with-output-file]
         [(regexp #rx"^call-with-input-file")
          'call-with-input-file]
         [_
          (raise-syntax-error 'parse-e "TODO" stx #'id)])]

      ;; Hacks for now. Still need this because fake:any/c ≠ any/c
      ;[(~literal null) -null]
      ;[(~literal empty) -null]
      [(~literal fake:any/c) 'any/c]
      [(~literal fake:none/c) 'none/c]
      [(~literal fake:not/c) 'not/c]
      [(~literal fake:and/c) 'and/c]
      [(~literal fake:or/c ) 'or/c]
      [(~literal fake:false/c) 'not]
      [(~literal fake:listof) 'listof]
      [(~literal fake:list/c) 'list/c]
      #;[(~literal fake:hash/c) 'hash/c] ; TODO doesn't work      

      ;; FIXME hack
      [x:id #:when (string-prefix? (symbol->string (syntax-e #'x)) "hash/c")
            'hash/c]
      [x:private-id (attribute x.name)]
      
      [i:identifier
       (or
        (parse-prim #'i)
        (parse-ref #'i))]))

  (define/contract (parse-ref id)
    (identifier? . -> . -x?)

    (define (lookup)
      (free-id-table-ref (env) id (λ () (raise-syntax-error 'parser "not in scope" id))))
    
    (match (identifier-binding id)
      ['lexical (-x (lookup) (syntax-ℓ id))]
      [#f (-x (lookup) (syntax-ℓ id))]
      [(list (app (λ (x)
                    (parameterize ([current-directory (directory-part (cur-mod))])
                      ;(printf "part: ~a~n" (directory-part (cur-mod)))
                      ;(printf "id: ~a~n" id)
                      (mod-path->mod-name
                       (resolved-module-path-name (module-path-index-resolve x)))))
                  src)
             _ _ _ _ _ _)
       #:when (not (equal? src 'Λ))
       (unless (∋ (modules-to-parse) src)
         (raise (exn:missing "missing" (current-continuation-marks) src (syntax-e id))))
       (unless (equal? src (cur-mod))
         (set-module-before! src (cur-mod)))
       (-x (-𝒾 (syntax-e id) src) (syntax-ℓ id))]
      [_
       (raise-syntax-error 'parser "don't know what this identifier means. It is possibly an unimplemented primitive." id)]))

  (define/contract parse-quote
    (scv-syntax? . -> . -e?)
    (syntax-parser
      [(~or e:number e:str e:boolean e:id e:keyword e:char) (-b (syntax-e #'e))]
      [(l . r)
       (-@ -cons
           (list (parse-quote #'l) (parse-quote #'r))
           (ℓ-with-id (syntax-ℓ #'(l . r)) (syntax-e #'r)))]
      [() -null]
      [h #:when (hash? (syntax->datum #'h)) (-•)] ; FIXME
      [#(x ...) (-@ 'vector (map parse-quote (syntax->list #'(x ...))) (syntax-ℓ #'(x ...)))]
      [r
       #:when (let ([re (syntax-e #'r)])
                (or (regexp? re)
                    (pregexp? re)
                    (byte-regexp? re)
                    (byte-pregexp? re)))
       (-b (syntax-e #'r))]
      [e (raise-syntax-error 'parse-quote "unsupported" #'e)]))

  ;; Parse given `formals` to extend environment
  (define/contract (parse-formals fml #:base [ρ₀ (env)])
    ([scv-syntax?] [#:base immutable-free-id-table?] . ->* . (values -formals? immutable-free-id-table?))

    (define (parse-binder id ρ)
      (define x (inc-id! id))
      (values x (free-id-table-set ρ id x)))

    (define (parse-binders ids ρ)
      (define-values (xs-rev ρ*)
        (for/fold ([xs-rev '()] [ρ ρ])
                  ([id (in-list ids)])
          (define-values (x ρ*) (parse-binder id ρ))
          (values (cons x xs-rev) ρ*)))
      (values (reverse xs-rev) ρ*))
    
    (syntax-parse fml
      [(x:id ...)
       (parse-binders (syntax->list #'(x ...)) ρ₀)]
      [rest:id
       (define-values (rest-name ρ) (parse-binder #'rest ρ₀))
       (values (-var '() rest-name) ρ)]
      [(x:id ... . rest:id)
       (define-values (inits ρ₁) (parse-binders (syntax->list #'(x ...)) ρ₀))
       (define-values (restid  ρ₂) (parse-binder #'rest ρ₁))
       (values (-var inits restid) ρ₂)])
    )

  (define/contract parse-require-spec
    (scv-syntax? . -> . -require-spec?)
    (syntax-parser
      [i:identifier (syntax-e #'i)]
      [spec (log-debug "parse-require-spec: ignore ~a~n" (syntax->datum #'spec))
            'dummy-require]))

  ;; For debugging only. Return scv-relevant s-expressions
  #;(define/contract (scv-relevant path)
    (path-string? . -> . any)
    (for/list ([stxᵢ (in-syntax-list (do-expand-file path))]
               #:unless (scv-ignore? stxᵢ))
      (syntax->datum stxᵢ)))

  (define/contract (module-level-id? id)
    (identifier? . -> . any)
    (match (identifier-binding id)
      [(list _ _ _ _ _ _ _) #t]
      [_ #f]))

  (define/contract (id-defining-module id)
    (identifier? . -> . any)
    (match (identifier-binding id)
      [(list (app (λ (x)
                    (parameterize ([current-directory (directory-part (cur-mod))])
                      (mod-path->mod-name
                       (resolved-module-path-name (module-path-index-resolve x)))))
                  src)
             _ _ _ _ _ _)
       src]
      [else (error 'id-defining-module "export module-level id, given ~a" (syntax-e id))]))

  (define/contract (id->𝒾 id)
    (identifier? . -> . -𝒾?)
    (-𝒾 (syntax-e id) (id-defining-module id)))

  (define (canonicalize-path p)
    (define p* (if (absolute-path? p) p (path->complete-path p)))
    (path->string (simplify-path p*)))
  )
