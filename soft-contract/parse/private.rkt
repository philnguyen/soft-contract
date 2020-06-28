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

(define-logger scv-parser)

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
      ((define (stx-for-each proc stxs fns)
         (for ([stx (in-list stxs)] [fn (in-list fns)])
           (parameterize ([cur-mod fn])
             (proc stx))))

       (define (stx-map proc stxs fns)
         (for/list ([stx (in-list stxs)] [fn (in-list fns)])
           (parameterize ([cur-mod fn])
             (proc stx))))

       (define (stxs->modules stxs fns)
         (begin
           (log-scv-parser-debug "fully expanded:")
           (for ([stx (in-list stxs)])
             (log-scv-parser-debug "~a" (pretty (syntax->datum stx)))))
         ;; Re-order the modules for an appropriate initilization order,
         ;; learned from side-effects of `parse-module`
         (define ans (sort (stx-map parse-module stxs fns) module-before? #:key -module-path))
         (begin
           (log-scv-parser-debug "internal ast:")
           (for ([m (in-list ans)])
             (log-scv-parser-debug "~a" (pretty m)))
           (log-scv-parser-debug "appendix:")
           (for ([ℓ (in-range (count-ℓ))])
             (log-scv-parser-debug "~a ↦ ~a" ℓ (ℓ->loc ℓ))))
         ans))

    (define (parse-stxs fns input-stxs)
      ;((listof syntax?) . -> . (listof -module?))

      (define (do-expand/path stx pth)
        (parameterize ([current-directory (path-only pth)])
          (do-expand stx)))

      (parameterize ([port-count-lines-enabled #t] ; TODO maybe no need
                     [struct-map (make-hash)]
                     [modules-to-parse (list->set fns)]
                     [id-occurence-count (make-hasheq)])
        (define stxs (map do-expand/path input-stxs fns))
        (stx-for-each figure-out-aliases! stxs fns)
        (stx-for-each figure-out-alternate-aliases!
                      (parameterize ([expander expand])
                        (map do-expand/path input-stxs fns))
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
      [(or '#%kernel '#%runtime '#%core) 'Λ]
      ['#%unsafe 'unsafe]
      ['|expanded module| (cur-mod)]
      [(or (? path-for-some-system?) (? path-string?)) (path->string (simplify-path p))]
      [(? list? l) (map (match-lambda
                          ['|expanded module| (cur-mod)]
                          [(and x (or (? path-for-some-system?) (? path-string?))) (path->string (simplify-path x))]
                          [x x])
                        l)]))

  (splicing-local
      ((define (for-each-module-level-form! on-module-level-form! stx)
         (let go! ([stx stx])
           (syntax-parse stx
             [((~literal module) id path ((~literal #%plain-module-begin) forms ...))
              (with-sub id
                (for-each go! (syntax->list #'(forms ...))))]
             [((~literal begin) form ...)
              (for-each go! (syntax->list #'(form ...)))]
             [_ (on-module-level-form! stx)]))))
    (define/contract (figure-out-aliases! stx)
      (scv-syntax? . -> . void?)
      (for-each-module-level-form!
       (syntax-parser
         #:literals (define-values #%plain-app quote)
         [(define-values (ex:id _) (#%plain-app do-partial-app _ _ (quote in:id) _ ...))
          #:when (equal? 'do-partial-app (syntax->datum #'do-partial-app)) ; TODO use "utils/evil"
          (define p (cur-path))
          (define 𝒾ᵢₙ (-𝒾 (syntax-e #'in) p))
          (define 𝒾ₑₓ (-𝒾 (syntax-e #'ex) p))
          (set-export-alias! 𝒾ₑₓ 𝒾ᵢₙ)]
         [_ (void)])
       stx))

    (define/contract (figure-out-alternate-aliases! stx)
      (scv-syntax? . -> . void?)

      (define extractor->wrapper (make-hash))
      (define wrapper-2->wrapper-1 (make-hash))
      (define wrapper-1->orig (make-hash))
      (define (connect m extractor wrapper)
        (define p (cur-path))
        (hash-set! m (-𝒾 (syntax-e extractor) p) (-𝒾 (syntax-e wrapper) p)))
      (for-each-module-level-form!
       (syntax-parser
         #:literals (define-values #%plain-app quote)
         [(~and stx (define-values (wrapper-1:id wrapper-2:id)
                      (#%plain-app f _ _ (quote name:id) _ _ _ ...)))
          #:when (eq? (syntax-e #'f) 'do-partial-app)
          (connect wrapper-2->wrapper-1 #'wrapper-2 #'wrapper-1)
          (connect wrapper-1->orig #'wrapper-1 #'name)]
         [(define-values (extractor:id)
            (#%plain-app f wrapper:id))
          #:when (eq? (syntax-e #'f) 'wrapped-extra-arg-arrow-extra-neg-party-argument)
          (connect extractor->wrapper #'extractor #'wrapper)]
         ;; after 7.4
         [(define-values (extractor:id)
            (#%plain-app f (#%plain-app _ _) wrapper:id _))
          #:when (eq? (syntax-e #'f) 'build->*-plus-one-acceptor)
          (connect extractor->wrapper #'extractor #'wrapper)]
         [_ (void)])
       stx)

      (for ([(extractor wrapper) (in-hash extractor->wrapper)])
        (define (with-orig orig)
          (set-alternate-alias! extractor orig #t)
          (set-alternate-alias! wrapper orig #f))
        (match (hash-ref wrapper-2->wrapper-1 wrapper #f)
          [(? values x) (match (hash-ref wrapper-1->orig x #f)
                          [(? values orig) (set-alternate-alias! x orig #f)
                                           (with-orig orig)]
                          [#f (with-orig x)])]
          [#f (with-orig (hash-ref wrapper-1->orig wrapper))]))))

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
         (log-scv-parser-debug "parsing (sub-)module ~a" (cur-path))
         (-module
          (cur-path)
          (for*/list ([formᵢ (in-list form-list)] #:when (care-about? formᵢ)
                      [?res (in-value (parse-module-level-form formᵢ))] #:when ?res)
            ?res)))]))

  ;; Convert syntax to `module-level-form`. May fail for unsupported forms.
  (define/contract (parse-module-level-form stx)
    (scv-syntax? . -> . (or/c #f -module-level-form?))
    #;(begin
      (printf "~nparse-module-level-form~n")
      (pretty-print (syntax->datum stx)))
    (syntax-parse stx
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

      ;; Hack for reading opaque bindings
      [d:scv-define-opaque
       (match-define (-𝒾 x _) (parse-id (attribute d.name)))
       (-define-values (list x) (-•) (next-ℓ! #'d))]
      
      [form (parse-general-top-level-form #'form)]))

  (define/contract parse-provide-spec
    (syntax? . -> . (listof -provide-spec?))
    (syntax-parser
      #:literals (quote #%plain-app)
      [d:scv-struct-out
       (define ℓ (attribute d.loc))
       (define st-doms (map parse-e (attribute d.field-contracts)))
       (define n (length st-doms))
       (match-define (and ctr-ref (-x (and s-id (-𝒾 s-name src)) _)) (parse-ref (attribute d.struct-id)))
       (define 𝒾* (resolve-struct-alias s-id))
       (unless (equal? (cur-path) (-𝒾-src 𝒾*))
         (set-struct-alias! (-𝒾 (-𝒾-name 𝒾*) (cur-path)) 𝒾*))
       (define st-p (-@ 'scv:struct/c (cons ctr-ref st-doms) ℓ))
       (define dec-constr ; TODO prim instead
         (let* ([ℓₖ (ℓ-with-id ℓ  'constructor)]
                [ℓₑ (ℓ-with-id ℓₖ 'provide)])
           (-p/c-item s-id (--> (-var st-doms #f) st-p ℓₖ) ℓₑ)))
       (define dec-pred
         (let* ([ℓₚ (ℓ-with-id ℓ  'predicate)]
                [ℓₑ (ℓ-with-id ℓₚ 'provide)])
           (-p/c-item (-𝒾 (format-symbol "~a?" s-name) src) ; TODO prim instead
                      (--> (-var (list 'any/c) #f) 'boolean? ℓₚ)
                      ℓₑ)))
       (define dec-acs
         (let ([all-acs (all-struct-accessors 𝒾*)])
           (unless (equal? (length all-acs) (length st-doms))
             (error 'parse-provide-spec "accesors: ~a, contracts: ~a" all-acs st-doms))
           (for/list ([ac (in-list all-acs)]
                      [st-dom st-doms]
                      [i (in-naturals)])
             (define ℓᵢ (ℓ-with-id ℓ i))
             (define ℓₑ (ℓ-with-id ℓᵢ 'provide))
             (-p/c-item ac (--> (-var (list st-p) #f) st-dom ℓᵢ) ℓₑ))))
       (list* dec-constr dec-pred dec-acs)]
      [d:scv-id-struct-out
       (match-define (and s-id (-𝒾 s-name src)) (parse-id (attribute d.struct-id)))
       (define 𝒾* (resolve-struct-alias s-id))
       (unless (equal? (cur-path) (-𝒾-src 𝒾*))
         (set-struct-alias! (-𝒾 (-𝒾-name 𝒾*) (cur-path)) 𝒾*))
       ;; FIXME: provide the primitives instead of their names?
       (list* s-id
              (-𝒾 (format-symbol "~a?" s-name) src)
              (map (λ (x) (-𝒾 x src)) (struct-direct-accessor-names 𝒾*)))]
      [(#%plain-app (~literal list) x:id c:expr)
       (list (-p/c-item (parse-id #'x) (parse-e #'c) (next-ℓ! #'x)))]
      [x:id (list (parse-id #'x))]))

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
            (define 𝒾* (id->𝒾 p))
            (set-parent-struct! 𝒾 (hash-ref (struct-map) 𝒾* 𝒾*)))])
       (define offset (struct-offset 𝒾))

       ;; Parse for direct field accessors/mutators
       (match-define (cons accs muts) (attribute d.accessors+mutators))

       (let ([acc-names (build-list (attribute d.field-count) (λ (i) (hash-ref accs i)))])
         (add-struct-info! 𝒾 acc-names (list->seteq (hash-keys muts))))
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
      [(define-values (_:identifier) (#%plain-app f (#%plain-app _ _) wrapper:id _))
       #:when (eq? (syntax-e #'f) 'build->*-plus-one-acceptor)
       #f]
      [(~and d (define-values (x:identifier ...) e))
       (define lhs (syntax->datum #'(x ...)))
       (for ([i lhs])
         (add-top-level! (-𝒾 i (cur-path))))
       (filter-out-junks (-define-values lhs (parse-e #'e) (syntax-ℓ #'d)))]
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
      [d:scv-struct-info-alias
       (-define-values (list (attribute d.lhs)) (parse-ref (attribute d.rhs)) (next-ℓ! #'d))]
      [(define-syntaxes _ ...) #f]
      [form (parse-e #'form)]))

  ;; Clueless HACK to get rid of junk definitions involving intermediate ids
  (define/contract filter-out-junks
    (-define-values? . -> . (or/c #f -define-values?))
    (match-lambda
      [(-define-values _ (-@ (-x (? -𝒾? 𝒾) _) _ _) _)
       #:when (get-export-alias 𝒾 (λ () #f))
       #f]
      [d d]))

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
          (λ () (raise (exn:missing (format "missing `~a` for `~a` from `~a`" (src-base f.src) (syntax-e #'f) (cur-mod))
                                    (current-continuation-marks) (src-base f.src) (syntax-e #'f))))))
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
      [(#%plain-app o:scv-fake-cmp c) (-comp/c (attribute o.op) (parse-e #'c) (next-ℓ! stx))]
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
      [c:scv-x/c (-rec/c (parse-ref (attribute c.ref)))]
      [(#%plain-app param/c:id e:expr)
       #:when (eq? (syntax-e #'param/c) 'parameter/c/proc)
       (-@ 'parameter/c (list (parse-e #'e)) (next-ℓ! stx))]

      ;; Literals
      [(~or v:str v:number v:boolean) (-b (syntax->datum #'v))] 
      [(#%declare _) (raise-syntax-error 'parse-e "TODO: #%declare ~a" stx)]
      [stx
       #:when (prefab-struct-key (syntax-e #'v))
       (raise-syntax-error 'parse-e "TODO: non-top-level struct" #'stx)]
      [(#%plain-app f x ...)
       (-@/simp (parse-e #'f) (parse-es #'(x ...)) (next-ℓ! stx))]

      ;; HACK for `parameterize`
      [(with-continuation-mark param-key:id (#%plain-app ext-param:id _ args ...) e ...)
       #:when (and (eq? (syntax-e #'param-key) 'parameterization-key)
                   (eq? (syntax-e #'ext-param) 'extend-parameterization))
       (define params
         (let loop ([bs (syntax->list #'(args ...))])
           (match bs
             [(list* x e bs*)
              (cons (cons (parse-e x) (parse-e e)) (loop bs*))]
             ['() '()])))
       (-parameterize params (-begin/simp (parse-es #'(e ...))) (next-ℓ! stx))]

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
          (define 𝒾* (get-export-alias 𝒾ₑₓ (λ () #f)))
          (cond [𝒾* (-x 𝒾* (next-ℓ! stx (cur-path)))]
                [(equal? (src-base src) (cur-mod)) (-b '|SCV-generated stub|)]
                [else (raise (exn:missing (format "missing `~a` for `~a` from `~a`" (src-base src) (syntax-e #'id0) (cur-mod))
                                          (current-continuation-marks) (src-base src) (syntax-e #'id0)))])]
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
      [(quote-syntax _ ...)
       (log-warning "Ignore ~a" (syntax->datum stx))
       (-b '|ignore quote-syntax|)]
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
      [c:scv-fake-lit (attribute c.real)]

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
    (identifier? . -> . (or/c -x? -b?))
    (define (lookup)
      (hash-ref (env) (syntax-e id)
                (λ ()
                  (define scope (hash-keys (env)))
                  (raise-syntax-error 'parser (format "`~a` not in scope (~a)" id scope)))))
    (define (err)
      (raise-syntax-error 'parser "don't know what this identifier means. It is possibly an unimplemented primitive." id))

    (match (identifier-binding id)
      ['lexical (-x (lookup) (next-ℓ! id))]
      [#f (-x (lookup) (next-ℓ! id))]
      [(list (app resolve-module-path src) _ _ _ _ _ _)
       (case src
         [(unsafe) (if (equal? (syntax-e id) 'unsafe-undefined) -undefined (err))]
         [(Λ) (err)]
         [else
          (define src:base (src-base src))
          (unless (∋ (modules-to-parse) src:base)
            (raise (exn:missing (format "missing `~a` for `~a` from `~a`" src:base (syntax-e id) (cur-mod))
                                (current-continuation-marks) src:base (syntax-e id))))
          (unless (equal? src:base (cur-mod))
            (set-module-before! src (cur-mod)))
          (-x (-𝒾 (syntax-e id) (src->path src)) (next-ℓ! id (cur-path)))])]
      [_ (err)]))

  (define (parse-id id)
    (cond [(parse-prim id) => values]
          [else (-x-_0 (parse-ref id))]))

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
      [(list (app resolve-module-path src) _ _ _ _ _ _) src]
      [else (error 'id-defining-module "export module-level id, given ~a" (syntax-e id))]))

  (define resolve-module-path
    (λ (x)
      (parameterize ([current-directory (directory-part (cur-mod))])
        ;(printf "part: ~a~n" (directory-part (cur-mod)))
        ;(printf "id: ~a~n" id)
        (mod-path->mod-name
         (resolved-module-path-name (module-path-index-resolve x))))))

  (define/contract (id->𝒾 id)
    (identifier? . -> . -𝒾?)
    (-𝒾 (syntax-e id) (src->path (id-defining-module id))))

  (define (canonicalize-path p)
    (define p* (if (absolute-path? p) p (path->complete-path p)))
    (path->string (simplify-path p*)))
  )
