#lang racket

(provide parser-helper@)

(require (prefix-in c: racket/contract/base)
         racket/splicing
         (only-in racket/string string-join)
         set-extras
         racket/unit
         ;racket/unsafe/ops
         web-server/private/util
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../primitives/signatures.rkt"
         ;; For extra constants
         syntax/parse
         syntax/parse/define
         syntax/modresolve
         syntax/id-table
         "hacks.rkt"
         "expand.rkt"
         (prefix-in fake: "../fake-contract.rkt")
         (prefix-in r5: r5rs)
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
  (define renaming? (hash/c symbol? symbol?))
  (define/contract env (parameter/c renaming?) (make-parameter (hasheq)))

  (define-syntax-rule (with-env ρ e ...) (parameterize ([env ρ]) e ...))
  (define next-ℓ!
    (let ([count (make-hash)])
      (λ (stx [?alt #f])
        (define l
          (match (ℓ->loc (syntax-ℓ stx))
            [(loc _ l c id) #:when ?alt (loc ?alt l c id)]
            [loc loc]))
        (define loc-count (hash-ref count l (λ () 0)))
        (hash-set! count l (add1 loc-count))
        (case loc-count
          [(0) (loc->ℓ l)]
          [else (ℓ-with-id (loc->ℓ l) (list 'unique loc-count))]))))
  
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

  (define/contract cur-mod (parameter/c string? #|TODO|#)
    (make-parameter "top-level"))
  (define/contract cur-subs (parameter/c (listof symbol?))
    (make-parameter '()))
  (define/contract cur-path (parameter/c string?)
    (make-parameter (cur-mod)))
  (define/contract (mk-path base subs) (string? (listof symbol?) . -> . string?)
    (string-join (cons base (map symbol->string subs)) ":"))
  (define-syntax-rule (with-sub sub body ...)
    (let ([new-subs (cons (syntax-e #'sub) (cur-subs))])
      (parameterize ([cur-subs new-subs]
                     [cur-path (mk-path (cur-mod) (cdr (reverse new-subs)))])
        body ...)))

  (define/contract (src-base s) ((or/c symbol? string? (cons/c string? (listof symbol?))) . -> . (or/c string? symbol?))
    (if (pair? s) (car s) s))
  (define/contract (src->path s) ((or/c symbol? string? (cons/c string? (listof symbol?))) . -> . (or/c string? symbol?))
    (if (pair? s) (mk-path (car s) (cdr s)) s))

  (splicing-local
      ((define (figure-out-alternate-aliases-in-modules! stxs fns)
         (for ([stx (in-list stxs)] [fn (in-list fns)])
           (parameterize ([cur-mod fn])
             (figure-out-alternate-aliases! stx))))

       (define (stx-for-each proc stxs fns)
         (for ([stx (in-list stxs)] [fn (in-list fns)])
           (parameterize ([cur-mod fn])
             (proc stx))))

       (define (stx-map proc stxs fns)
         (for/list ([stx (in-list stxs)] [fn (in-list fns)])
           (parameterize ([cur-mod fn])
             (proc stx))))

       (define (stxs->modules stxs fns)
         ;; Re-order the modules for an appropriate initilization order,
         ;; learned from side-effects of `parse-module`
         (sort (stx-map parse-module stxs fns) module-before? #:key -module-path)))

    (define (parse-stxs input-stxs)
      ;((listof syntax?) . -> . (listof -module?))

      (define stx->name
        (syntax-parser
          [((~literal module) name:id _ _ ...)
           (id-defining-module #'name)]))

      (parameterize ([struct-map (make-hash)]
                     [id-occurence-count (make-hasheq)])
        (define fns (map stx->name input-stxs))
        (define stxs (map do-expand input-stxs))
        (stx-for-each figure-out-aliases! stxs fns)
        (stx-for-each figure-out-alternate-aliases!
                      (parameterize ([expander expand])
                        (map do-expand input-stxs))
                      fns)
        (stxs->modules stxs fns)))

    (define (parse-files fns)
      ;((listof path-string?) . -> . (listof -module?))

      (parameterize ([port-count-lines-enabled #t]
                     [struct-map (make-hash)]
                     [modules-to-parse (list->set fns)]
                     [id-occurence-count (make-hasheq)])
        (define stxs (map do-expand-file fns))
        (stx-for-each figure-out-aliases! stxs fns)
        (stx-for-each figure-out-alternate-aliases!
                      (parameterize ([expander expand])
                        (map do-expand-file fns))
                      fns)
        (stxs->modules stxs fns))))

  (define scv-syntax? (and/c syntax? (not/c scv-ignore?)))

  (define (mod-path->mod-name p)
    (match p ; hacks
      [(or '#%kernel '#%runtime) 'Λ]
      ['#%unsafe 'unsafe]
      [(and (? symbol?) (app symbol->string "expanded module")) (cur-mod)]
      [(or (? path-for-some-system?) (? path-string?)) (path->string (simplify-path p))]
      [(cons p q) (cons (cur-mod) q)]))

  (define/contract (figure-out-aliases! stx)
    (scv-syntax? . -> . void?)

    (define on-module-level-form!
      (syntax-parser
        #:literals (define-values #%plain-app quote)
        [(define-values (ex:id _) (#%plain-app do-partial-app _ _ (quote in:id) _ ...))
         #:when (equal? 'do-partial-app (syntax->datum #'do-partial-app)) ; TODO use "utils/evil"
         (define p (cur-path))
         (define 𝒾ᵢₙ (-𝒾 (syntax-e #'in) p))
         (define 𝒾ₑₓ (-𝒾 (syntax-e #'ex) p))
         (set-export-alias! 𝒾ₑₓ 𝒾ᵢₙ)]
        [s (figure-out-aliases! #'s)]))
    
    (syntax-parse stx
      [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
       (with-sub id
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
           (#%plain-app f _ _ (quote name:id) _ _ _ ...)))
         #:when (eq? (syntax-e #'f) 'do-partial-app)
         (define p (cur-path))
         (hash-set! wrapper->name (-𝒾 (syntax-e #'wrapper) p) (-𝒾 (syntax-e #'name) p))]
        [(define-values (extractor:id)
           (#%plain-app f wrapper:id))
         #:when (eq? (syntax-e #'f) 'wrapped-extra-arg-arrow-extra-neg-party-argument)
         (define p (cur-path))
         (hash-set! extractor->wrapper (-𝒾 (syntax-e #'extractor) p) (-𝒾 (syntax-e #'wrapper) p))]
        [_ (void)]))

    (let go! ([stx stx])
      (syntax-parse stx
        [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
         (with-sub id
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
      [(~and m ((~literal module) _ ...)) (parse-module #'m)]
      [((~literal begin) form ...)
       (-begin/simp (map parse-top-level-form (syntax->list #'(form ...))))]
      [((~literal #%expression) e) (parse-e #'e)]
      [form (parse-general-top-level-form #'form)]))

  (define parse-module
    (syntax-parser
      [(~or ((~literal module) id path ((~literal #%plain-module-begin) forms ...))
            ((~literal module) id path forms ...))

       (define care-about?
         (syntax-parser
           [((~literal module) (~literal configure-runtime) _ ...) #f]
           [form (scv-syntax? #'form)]))

       (define form-list ; Move "provide" clauses to the end
         (let-values ([(body provides)
                       (partition (syntax-parser
                                    [_:scv-provide #f]
                                    [_ #t])
                                  (syntax->list #'(forms ...)))])
           (append body provides)))

       (with-sub id
         (-module
          (cur-path)
          (for*/list ([formᵢ (in-list form-list)] #:when (care-about? formᵢ)
                      [?res (in-value (parse-module-level-form formᵢ))] #:when ?res)
            ?res)))]))

  ;; Convert syntax to `module-level-form`. May fail for unsupported forms.
  (define/contract parse-module-level-form
    (scv-syntax? . -> . (or/c #f -module-level-form?))
    (syntax-parser
      #:literals (module module* #%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                  call-with-values)
      ;; inline parsing of `submodule-form`s
      [(~and m ((~literal module) _ ...)) (parse-module #'m)]
      [(~and m ((~literal module*) _ ...))
       (raise-syntax-error 'parse-e "TODO: module* ~a" #'m)]
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
      
      [form (parse-general-top-level-form #'form)]))

  (define/contract parse-provide-spec
    (syntax? . -> . (listof -provide-spec?))
    (syntax-parser
      #:literals (quote #%plain-app)
      [d:scv-struct-out
       (define ℓ (attribute d.loc))
       (define s-name (attribute d.name))
       (define 𝒾 (-𝒾 s-name (cur-path)))
       (define st-doms (map parse-e (attribute d.field-contracts)))
       (define n (length st-doms))
       (define st-p (-@ 'scv:struct/c (cons (-st-mk 𝒾) st-doms) ℓ))
       (define dec-constr
         (let* ([ℓₖ (ℓ-with-id ℓ  'constructor)]
                [ℓₑ (ℓ-with-id ℓₖ 'provide)])
           (-p/c-item s-name (--> (-var st-doms #f) st-p ℓₖ) ℓₑ)))
       (define dec-pred
         (let* ([ℓₚ (ℓ-with-id ℓ  'predicate)]
                [ℓₑ (ℓ-with-id ℓₚ 'provide)])
           (-p/c-item (format-symbol "~a?" s-name)
                      (--> (-var (list 'any/c) #f) 'boolean? ℓₚ)
                      ℓₑ)))
       (define dec-acs
         (let ([offset (struct-offset 𝒾)])
           (for/list ([ac (in-list (attribute d.field-names))]
                      [st-dom st-doms]
                      [i (in-naturals)] #:when (>= i offset))
             (define ℓᵢ (ℓ-with-id ℓ i))
             (define ℓₑ (ℓ-with-id ℓᵢ 'provide))
             (define ac-name (format-symbol "~a-~a" s-name ac))
             (-p/c-item ac-name (--> (-var (list st-p) #f) st-dom ℓᵢ) ℓₑ))))
       (list* dec-constr dec-pred dec-acs)]
      [(#%plain-app (~literal list) x:id c:expr)
       (list (-p/c-item (syntax-e #'x) (parse-e #'c) (next-ℓ! #'x)))]
      [x:id
       (list (syntax-e #'x))]))

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
       (set-alternate-alias-id! (cur-path) (syntax-e #'lifted.0))
       #f]
      [(#%plain-app call-with-values (#%plain-lambda () e) print-values:id)
       #:when (equal? 'print-values (syntax->datum #'print-values))
       (parse-e #'e)]

      [d:scv-struct-decl
       (define ctor (attribute d.constructor-name))
       (define 𝒾 (-𝒾 ctor (cur-path)))
       (hash-set! (struct-map) (id->𝒾 (attribute d.extra-constructor-name)) 𝒾)
       ;; Figure out parent struct
       (cond
         [(attribute d.?parent) =>
          (λ (p)
            (set-parent-struct! 𝒾 (hash-ref (struct-map) (id->𝒾 p))))])
       (define offset (struct-offset 𝒾))

       ;; Parse for direct field accessors/mutators
       (match-define (cons accs muts) (attribute d.accessors+mutators))
       
       (add-struct-info! 𝒾 (attribute d.field-count) (list->seteq (hash-keys muts)))
       (for ([name (in-sequences (list ctor (attribute d.predicate-name))
                                 (hash-values accs)
                                 (hash-values muts))])
         (add-top-level! (-𝒾 name (cur-path))))
       (let ([acc-list (hash->list accs)]
             [mut-list (hash->list muts)])
         (-define-values
          `(,ctor ,(attribute d.predicate-name) ,@(map cdr acc-list) ,@(map cdr mut-list))
          (-@ 'values
              `(,(-st-mk 𝒾)
                ,(-st-p 𝒾)
                ,@(for/list ([i (in-list (map car acc-list))])
                    (-st-ac 𝒾 (+ offset i)))
                ,@(for/list ([i (in-list (map car mut-list))])
                    (-st-mut 𝒾 (+ offset i))))
              (next-ℓ! #'d))
          (syntax-ℓ #'d)))]
      [;; Hack ignoring generated garbage by `struct`
       (define-values (_:identifier) (#%plain-app f:id _:id))
       #:when (equal? 'wrapped-extra-arg-arrow-extra-neg-party-argument (syntax-e #'f))
       #f]
      ; FIXME: separate case hack to "close" recursive contract
      [(~and d (define-values (x:identifier) e))
       (define lhs (syntax-e #'x))
       (define rhs (parse-e #'e))
       (define frees (free-x/c rhs))
       (define ℓ (syntax-ℓ #'d))
       (cond
         [(set-empty? frees)
          (add-top-level! (-𝒾 lhs (cur-path)))
          (-define-values (list lhs) rhs ℓ)]
         [(set-empty? (set-remove frees lhs))
          (define x (+x! (format-symbol "~a_~a" 'rec lhs)))
          (add-top-level! (-𝒾 lhs (cur-path)))
          (-define-values (list lhs) (-μ/c x (e/ lhs (-x x (syntax-ℓ #'e)) rhs)) ℓ)]
         [else
          (raise-syntax-error
           'recursive-contract
           "arbitrary recursive contract reference not supported for now."
           #'(define-values (x) e)
           #'e)])]
      [(~and d (define-values (x:identifier ...) e))
       (define lhs (syntax->datum #'(x ...)))
       (for ([i lhs])
         (add-top-level! (-𝒾 i (cur-path))))
       (-define-values lhs (parse-e #'e) (syntax-ℓ #'d))]
      [(#%require spec ...) #f]
      [(~and d (define-syntaxes (k:id) ; constructor alias
                 (~and rhs
                       (#%plain-app
                        (~literal make-self-ctor-checked-struct-info)
                        _ _
                        (#%plain-lambda () (quote-syntax k1:id))))))
       (define lhs (syntax-e #'k1))
       (add-top-level! (-𝒾 lhs (cur-path)))
       (-define-values (list lhs) (-x (-𝒾 (syntax-e #'k) (cur-path)) (next-ℓ! #'d)) (next-ℓ! #'d))]
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
       (-error "incomplete pattern matching" (next-ℓ! stx))]

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
      [(#%plain-app (~literal raise) args ...)
       (-@ 'raise (list (-b (string-join (for/list ([arg (in-list (syntax->list #'(args ...)))])
                                           (format "~a" (syntax->datum arg))))))
           (next-ℓ! stx))]

      ;; HACK for immediate uses of `list`
      [(#%plain-app (~literal list) e ...)
       (-list
        (for/list ([e (in-syntax-list #'(e ...))])
          (cons (next-ℓ! e) (parse-e e))))]

      ;; HACK for immediate uses of accessors
      [(#%plain-app (~literal cadr) e)
       (match-define (list ℓ₁ ℓ₂) (ℓ-with-ids (next-ℓ! stx) 2))
       (-@ -car (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)]
      [(#%plain-app (~literal caddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃) (ℓ-with-ids (next-ℓ! stx) 3))
       (-@ -car (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)]
      [(#%plain-app (~literal cadddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃ ℓ₄) (ℓ-with-ids (next-ℓ! stx) 4))
       (-@ -car (list (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)) ℓ₄)]
      [(#%plain-app (~literal cddddr) e)
       (match-define (list ℓ₁ ℓ₂ ℓ₃ ℓ₄) (ℓ-with-ids (next-ℓ! stx) 4))
       (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (-@ -cdr (list (parse-e #'e)) ℓ₁)) ℓ₂)) ℓ₃)) ℓ₄)]

      ;; HACK for treating `apply` specially for precision.
      ;; This simply bypasses reading `apply` as wrapped reference to primitive
      [(#%plain-app f:id x ...)
       #:when #|HACK can't use ~literal for some reason|# (equal? 'apply (syntax-e #'f))
       (-@ 'apply (parse-es #'(x ...)) (next-ℓ! stx))]

      ;; tmp HACK for varargs
      [(#%plain-app o e ...)
       #:when (syntax-parse #'o
                [(~or (~literal +) (~literal -) (~literal *) (~literal /)) #t]
                [_ #f])
       (define o.name (syntax-e #'o))
       (define ℓ (next-ℓ! stx))
       (match (parse-es #'(e ...))
         [(list e) e]
         [(list e₁ e* ...)
          (for/fold ([e e₁]) ([eᵢ (in-list e*)] [i (in-naturals)])
            (-@ o.name (list e eᵢ) (ℓ-with-id ℓ i)))])]

      ;; HACKs for `variable-refererence-constant?`
      [app:indirect-app
       (-@ (attribute app.fun-name) (parse-es #'app.args) (next-ℓ! #'app))]

      ;; HACK for ignoring junks generated by `in-list` and friends
      [_:scv-ignored (-b (void))]

      ;; HACK for figuring out exports from non-faked files
      [(#%plain-app f:id lifted.0 args ...)
       #:when (equal? (syntax-e #'lifted.0) (get-alternate-alias-id (cur-mod) (λ () #f)))
       (define f.src (id-defining-module #'f))
       (match-define (cons f-resolved wrap?)
         (get-alternate-alias
          (-𝒾 (syntax-e #'f) (src->path f.src))
          (λ () (raise (exn:missing "missing" (current-continuation-marks) (src-base f.src) (syntax-e #'f))))))
       (set-module-before! (src-base f.src) (cur-mod))
       (define f-ref (-x f-resolved (next-ℓ! #'f (cur-path))))
       (cond
         [wrap? (-@ f-ref (parse-es #'(args ...)) (next-ℓ! stx))]
         [(and (not wrap?) (null? (syntax->list #'(args ...)))) f-ref]
         [else (error 'parser "my understanding is wrong")])]
      

      ;;; Contracts
      ;; Terminating contract
      [(~literal fake:terminating/c) 'scv:terminating/c]
      ;; Parametric contract
      [ctc:scv-parametric->/c
       (define-values (xs ρ) (parse-formals (attribute ctc.params)))
       (match-define (-var xs₀ #f) xs)
       (-∀/c xs₀ (with-env ρ (parse-e (attribute ctc.body))) (syntax-ℓ #'ctc))]
      ;; Dependent contract (also subsumes non-dependent one)
      [e:scv-->i
       (define stx-init-doms (attribute e.init-domains))
       (define stx-rest-dom  (attribute e.rest-domain))
       (define stx-ranges    (attribute e.ranges))
       (define dom-names
         (let ([dom-name (syntax-parser [dom:named-dom (attribute dom.name)])])
           `(,@(map dom-name stx-init-doms)
             ,@(match stx-rest-dom
                 [(? values c) (list (dom-name c))]
                 [#f '()])
             ,@(match stx-ranges
                 [(? values ds) (map dom-name ds)]
                 [#f '()]))))
       (define-values (_ ρ) (parse-binders dom-names))
       (with-env ρ
         (define cs (map parse-named-domain stx-init-doms))
         (define cr (and stx-rest-dom (parse-named-domain stx-rest-dom)))
         (define ds (and stx-ranges (map parse-named-domain stx-ranges)))
         (cond [(first-forward-ref `(,@cs ,@(if cr (list cr) '()) ,@(if ds ds '()))) =>
                (λ (x) (error 'scv "forward reference to `~a` in `->i` is not yet supported, probably never will be" x))])
         (define ctc (-->i (-var cs cr) ds))
         (if (attribute e.total?)
             (-@ 'and/c (list ctc 'scv:terminating/c) (next-ℓ! #'c))
             ctc))]
      [e:scv-case->
       (case-->
        (map
         (match-lambda
           [(list inits ?rest rng stx)
            (define dom (-var (map parse-e inits) (and ?rest (parse-e ?rest))))
            (--> dom (parse-e rng) (next-ℓ! stx))])
         (attribute e.cases)))]
      [(#%plain-app (~literal fake:list/c) c ...)
       (define args
         (for/list ([cᵢ (in-syntax-list #'(c ...))])
           (cons (next-ℓ! cᵢ) (parse-e cᵢ))))
       (-list/c args)]
      [(#%plain-app (~literal fake:box/c) c)
       (-box/c (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:vector/c) c ...)
       (-@ 'vector/c (parse-es #'(c ...)) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:vectorof) c)
       (-@ 'vectorof (list (parse-e #'c)) (next-ℓ! stx))]
      [c:scv-struct/c
       (-@ 'scv:struct/c (map parse-e (cons (attribute c.name) (attribute c.fields))) (next-ℓ! #'c))]
      [(#%plain-app (~literal fake:=/c) c) (-comp/c '= (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:>/c) c) (-comp/c '> (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:>=/c) c) (-comp/c '>= (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:</c) c) (-comp/c '< (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:<=/c) c) (-comp/c '<= (parse-e #'c) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:between/c) l h)
       (define ℓ (next-ℓ! stx))
       (-@ 'and/c (list 'real?
                        (-comp/c '>= (parse-e #'l) (ℓ-with-id ℓ 'lo))
                        (-comp/c '<= (parse-e #'h) (ℓ-with-id ℓ 'hi)))
           ℓ)]
      [(#%plain-app (~literal fake:flat-contract) c) (parse-e #'c)]
      [(#%plain-app (~literal fake:cons/c) c d)
       (-cons/c (parse-e #'c) (parse-e #'d) (next-ℓ! stx))]
      [(#%plain-app (~literal fake:one-of/c) c ...)
       (-@ 'one-of/c (parse-es #'(c ...)) (next-ℓ! stx))]
      [c:scv-x/c (-x/c.tmp (attribute c.ref))]

      ;; Literals
      [(~or v:str v:number v:boolean) (-b (syntax->datum #'v))] 
      [(#%declare _) (raise-syntax-error 'parse-e "TODO: #%declare ~a" stx)]
      [stx
       #:when (prefab-struct-key (syntax-e #'v))
       (raise-syntax-error 'parse-e "TODO: non-top-level struct" #'stx)]
      [(#%plain-app f x ...)
       (-@/simp (parse-e #'f) (parse-es #'(x ...)) (next-ℓ! stx))]
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
          (define 𝒾ₑₓ (-𝒾 (syntax-e #'id0) (src->path src)))
          (set-module-before! (src-base src) (cur-mod))
          (define 𝒾* (get-export-alias 𝒾ₑₓ (λ () (raise (exn:missing "missing" (current-continuation-marks) (src-base src) (syntax-e #'id0))))))
          (-x 𝒾* (next-ℓ! stx (cur-path)))]
         [_
          (-begin/simp (parse-es #'(e ...)))])]
      [(begin0 e₀ e ...) (-begin0 (parse-e #'e₀) (parse-es #'(e ...)))]
      [(if i t e)
       (-if/simp (parse-e #'i) (parse-e #'t) (parse-e #'e) (syntax-ℓ stx))]
      [(let-values (bindings ...) b ...)
       (define-values (bindings-rev ρ)
         (for/fold ([bindings-rev '()] [ρ (env)])
                   ([bnd (in-syntax-list #'(bindings ...))])
           (syntax-parse bnd
             [((x ...) e)
              (define-values (xs ρ*) (parse-formals #'(x ...) #:base ρ))
              (values (cons (cons (-var-init xs) (parse-e #'e)) bindings-rev) ρ*)])))
       (-let-values/simp (reverse bindings-rev)
                         (with-env ρ (-begin/simp (parse-es #'(b ...))))
                         (next-ℓ! stx))]
      [(set! i:identifier e)
       (match-define (-x x _) (parse-ref #'i))
       (set-assignable! x)
       (-set! x (parse-e #'e) (syntax-ℓ stx))]
      [(#%plain-lambda fmls b ...+)
       (define-values (xs ρ) (parse-formals #'fmls))
       ;; put sequence back to `(begin ...)` to special cases of fake-contracts
       (-λ xs (with-env ρ (parse-e #'(begin b ...))) (syntax-ℓ stx))]
      
      [(case-lambda [fml bodies ...+] ...)
       (-case-λ
        (for/list ([fmlᵢ (in-syntax-list #'(fml ...))]
                   [bodiesᵢ (in-syntax-list #'((bodies ...) ...))])
          ;; Compute case arity and extended context for RHS
          (define-values (xsᵢ ρᵢ) (parse-formals fmlᵢ))
          (-λ xsᵢ (with-env ρᵢ (-begin/simp (parse-es bodiesᵢ))) (syntax-ℓ stx)))
        (next-ℓ! stx))]
      [(letrec-values () b ...) (-begin/simp (parse-es #'(b ...)))]
      [(letrec-values (bindings ...) b ...)
       (define-values (lhss-rev ρ)
         (for/fold ([lhss-rev '()] [ρ (env)])
                   ([bnd (in-syntax-list #'(bindings ...))])
           (syntax-parse bnd
             [((x ...) _)
              (define-values (lhs ρ*) (parse-formals #'(x ...) #:base ρ))
              (for-each set-assignable! (-var-init lhs))
              (values (cons (-var-init lhs) lhss-rev) ρ*)])))
       (-letrec-values
        (for/list ([lhs (in-list (reverse lhss-rev))]
                   [bnd (in-syntax-list #'(bindings ...))])
          (syntax-parse bnd
            [(_ eₓ) (cons lhs (with-env ρ (parse-e #'eₓ)))]))
        (with-env ρ (-begin/simp (parse-es #'(b ...))))
        (next-ℓ! stx))]
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
      [(~literal fake:between/c) 'between/c]
      [(~literal fake:flat-contract) 'values]
      [(~literal fake:hash/c) 'hash/c] ; TODO doesn't work
      [(~literal fake:set/c) 'set/c]
      [(~literal fake:dynamic-mon) 'scv:mon]
      [(~literal fake:contract?) 'contract?]

      ;; FIX Tmp. Hacks for Scheme programs
      [(~literal r5:pair?) -cons?]
      [(~literal r5:cdr) -cdr]
      [(~literal r5:car) -car]
      [(~literal r5:cons) -cons]
      [(~literal r5:set-car!) -set-car!]
      [(~literal r5:set-cdr!) -set-cdr!]
      [(~literal r5:memq) 'memq]
      [(~literal r5:list->mlist) 'list]
      [(~literal r5:vector->list) 'vector->list]
      [(~literal r5:list->vector) 'list->vector]
      [(~literal r5:display) 'display]
      [(~literal r5:length) 'length]
      [(~literal r5:assq) 'assq]
      [(~literal r5:map) 'map]
      [(~literal r5:caddr) 'caddr]
      [(~literal r5:caaaar) 'caaaar]
      [(~literal r5:append) 'append]
      

      ;; FIXME hack
      [x:id #:when (string-prefix? (symbol->string (syntax-e #'x)) "hash/c")
            'hash/c]
      [x:private-id (attribute x.name)]
      [i:identifier
       (or
        (parse-prim #'i)
        (parse-ref #'i))]))

  (define/contract (parse-named-domain stx)
    (scv-syntax? . -> . -dom?)
    (syntax-parse stx
      [dom:named-dom
       (define (lookup x) (hash-ref (env) (syntax-e x)))
       (define x (lookup (attribute dom.name)))
       (define c (parse-e (attribute dom.body)))
       (define ?dep
         (match (attribute dom.dependency)
           [#f #f]
           [zs (map lookup zs)]))
       (-dom x ?dep c (syntax-ℓ #'dom))]))

  (define/contract (parse-ref id)
    (identifier? . -> . -x?)

    (define (lookup)
      (hash-ref (env) (syntax-e id)
                (λ ()
                  (define scope (hash-keys (env)))
                  (raise-syntax-error 'parser (format "`~a` not in scope (~a)" id scope)))))

    (match (identifier-binding id)
      ['lexical (-x (lookup) (next-ℓ! id))]
      [#f (-x (lookup) (next-ℓ! id))]
      [(list (app (λ (x)
                    (parameterize ([current-directory (directory-part (cur-mod))])
                      ;(printf "part: ~a~n" (directory-part (cur-mod)))
                      ;(printf "id: ~a~n" id)
                      (mod-path->mod-name
                       (resolved-module-path-name (module-path-index-resolve x)))))
                  src)
             _ _ _ _ _ _)
       #:when (not (equal? src 'Λ))
       (define src:base (src-base src))
       (unless (∋ (modules-to-parse) src:base)
         (raise (exn:missing "missing" (current-continuation-marks) src:base (syntax-e id))))
       (unless (equal? src:base (cur-mod))
         (set-module-before! src (cur-mod)))
       (-x (-𝒾 (syntax-e id) (src->path src)) (next-ℓ! id (cur-path)))]
      [_
       (raise-syntax-error 'parser "don't know what this identifier means. It is possibly an unimplemented primitive." id)]))

  (define/contract parse-quote
    (scv-syntax? . -> . -e?)
    (syntax-parser
      [(~or e:number e:str e:boolean e:id e:keyword e:char) (-b (syntax-e #'e))]
      [(l . r)
       (-@ -cons
           (list (parse-quote #'l) (parse-quote #'r))
           (ℓ-with-id (next-ℓ! #'(l . r)) (syntax-e #'r)))]
      [() -null]
      [h #:when (hash? (syntax->datum #'h)) (-•)] ; FIXME
      [#(x ...) (-@ 'vector (map parse-quote (syntax->list #'(x ...))) (next-ℓ! #'(x ...)))]
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
    ([scv-syntax?] [#:base renaming?] . ->* . (values -formals? renaming?)) 
    (syntax-parse fml
      [(x:id ...)
       (define-values (xs ρ) (parse-binders (syntax->list #'(x ...)) #:base ρ₀))
       (values (-var xs #f) ρ)]
      [rest:id
       (define-values (rest-name ρ) (parse-binder #'rest #:base ρ₀))
       (values (-var '() rest-name) ρ)]
      [(x:id ... . rest:id)
       (define-values (inits ρ₁) (parse-binders (syntax->list #'(x ...)) #:base ρ₀))
       (define-values (restid  ρ₂) (parse-binder #'rest #:base ρ₁))
       (values (-var inits restid) ρ₂)]))

  (define/contract (parse-binder id #:base [ρ (env)])
    ([identifier?] [#:base renaming?] . ->* . (values symbol? renaming?))
    (define x (inc-id! id))
    (values x (hash-set ρ (syntax-e id) x)))

  (define/contract (parse-binders ids #:base [ρ (env)])
    ([(listof identifier?)] [#:base renaming?] . ->* . (values (listof symbol?) renaming?))
    (define-values (xs-rev ρ*)
      (for/fold ([xs-rev '()] [ρ ρ])
                ([id (in-list ids)])
        (define-values (x ρ*) (parse-binder id #:base ρ))
        (values (cons x xs-rev) ρ*)))
    (values (reverse xs-rev) ρ*))

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
