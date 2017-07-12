#lang typed/racket/base

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/definition.rkt"
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt")

(begin-for-syntax

  (define-syntax-rule (with-hack:make-available (src id ...) e ...)
    (with-syntax ([id (format-id src "~a" 'id)] ...) e ...))

  (define-syntax-rule (hack:make-available src id ...)
    (begin (define/with-syntax id (format-id src "~a" 'id)) ...))

  (define/contract hack:resolve-alias
    (identifier? . -> . syntax?)
    (syntax-parser
      [(~or (~literal cons?) (~literal pair?)) #'-cons?]
      [(~or (~literal box?)) #'-box?]
      [p:id #''p]))

  (define/contract (gen-program entry table)
    (symbol? (hash/c symbol? (listof syntax?)) . -> . (listof syntax?))
    (for/fold ([acc (hash-ref table entry)])
              ([(f es) (in-hash table)] #:unless (equal? f entry))
      (cons #`(define (#,(->id f) [#,(-Γ) : -Γ]) #,@es) acc)))
  
  ;; Global parameters that need to be set up for each `def-prim`
  (define-parameter/contract
    ; identifiers available to function body
    [-$ identifier? #f]
    [-Σ identifier? #f]
    [-Γ identifier? #f]
    [-ℒ identifier? #f]
    [-⟪ℋ⟫ identifier? #f]
    [-Ws identifier? #f]
    [-o identifier? #f]
    [-Wₙ (listof identifier?) #f]
    [-bₙ (listof identifier?) #f]
    [-sₙ (listof identifier?) #f]
    [-W* (or/c #f identifier?) #f]
    [-b* identifier? #f]
    [-s* identifier? #f]
    ; from decomposing `def-prim` clause
    [-sig syntax? #f]
    [-refs (listof #|sig|# syntax?) #f]
    [-errs (listof (listof #|dom|# syntax?)) #f]
    [-lift? boolean? #f]
    ; given blame-producing expression, generate failure expression
    [-gen-blm (syntax? . -> . syntax?) #f]
    [-volatile? boolean? #f]
    ;; exts
    [-ℓ identifier? #f]
    [-⟦k⟧ identifier? #f]
    )

  (define/contract (gen-ans d)
    (syntax? . -> . syntax?)
    #`(error 'gen-ans "TODO: ~a" '#,(syntax->datum d)))

  ;; Generate the expression producing contract `c`
  ;; along with expressions performing neccessary allocations
  (define/contract (gen-alloc ℓ c)
    (identifier? syntax? . -> . syntax?)
    (syntax-parse c
      [((~literal ->) cₓ ... d)
       (hack:make-available (-o) σ⊕V!)
       #`(let ([αℓs (list
                     #,@(for/list ([cₓ (in-list (syntax->list #'(cₓ ...)))]
                                   [i (in-naturals)])
                          #`(let ([⟪α⟫ (-α->⟪α⟫ '#,cₓ)]
                                  [ℓ (ℓ-with-id #,ℓ #,i)])
                              (σ⊕V! #,(-Σ) ⟪α⟫ #,(gen-alloc #'ℓ cₓ))
                              (-⟪α⟫ℓ ⟪α⟫ ℓ))))]
               [βℓs
                (list (let ([⟪β⟫ (-α->⟪α⟫ 'd)]
                            [ℓ (ℓ-with-id #,ℓ #,(length (syntax->list #'(cₓ ...))))])
                        (σ⊕V! #,(-Σ) ⟪β⟫ #,(gen-alloc #'ℓ #'d))
                        (-⟪α⟫ℓ ⟪β⟫ ℓ)))])
           (-=> αℓs βℓs #,ℓ))]
      [c:id #'(quote c)]
      [_ (error 'gen-alloc "unhandled: ~a" (syntax->datum c))]))

  ;; Generate expression wrapping function contract `c` around `V`
  (define/contract (gen-func-wrap c V s)
    (syntax? syntax? syntax? . -> . syntax?)
    (hack:make-available (-o) σ⊕V!)
    ;; be careful not to use `V` twice
    ;; FIXME ℓ maybe wrong here
    #`(let* ([ℓ (loc->ℓ (loc '#,(-o) 0 0 '()))]
             [l³ (-l³ (ℓ-src ℓ) '#,(-o) '#,(-o))]
             [grd #,(gen-alloc #'ℓ c)]
             [⟪α⟫ (-α->⟪α⟫ (-α.fn #,s #,(-ℒ) #,(-⟪ℋ⟫) (ℓ-src ℓ) #,(-Γ)))])
        (σ⊕V! #,(-Σ) ⟪α⟫ #,V)
        (-Ar grd ⟪α⟫ l³)))

  ;; Generate expression wrapping contract `c` around `V`
  (define/contract (gen-wrap c V s)
    (syntax? syntax? syntax? . -> . syntax?)
    (hack:make-available (-o) V+)
    ;; be careful not to use `V` twice
    (syntax-parse c
      [((~literal ->) _ ...) (gen-func-wrap c V s)]
      [((~literal and/c) c*:id ...) #`(V+ (-Σ-σ #,(-Σ)) #,V (seteq 'c* ...))]
      ;[((~literal and/c) c*    ...) (foldr gen-wrap V (syntax->list #'(c* ...)))]
      [c:id #`(V+ (-Σ-σ #,(-Σ)) #,V 'c)]
      [_ (error 'gen-wrap-clause "unhandled: ~a" (syntax->datum #'c))]))

  ;; Generate re-definitions of variables that should be wrapped in higher-order contracts
  (define/contract (gen-arg-wraps body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:hf (-sig))
    (define eᵢs
      (for/list ([W (in-list (-Wₙ))]
                 [c (in-list (attribute sig.init))])
        (gen-wrap c #`(-W¹-V #,W) #`(-W¹-t #,W))))
    (define/with-syntax (clauses-rest ...) #|TODO|# '())
    (list
     #`(let (#,@(for/list ([Wᵢ (in-list (-Wₙ))]
                           [eᵢ (in-list eᵢs)])
                  #`[#,Wᵢ (-W¹ #,eᵢ (-W¹-t #,Wᵢ))])
             clauses-rest ...)
         #,@body)))

  ;; Generate guards for identifier `x` based on given contract `c`
  (define/contract (gen-base-guard c x)
    (syntax? identifier? . -> . (or/c syntax? #f))
    (let go ([c c])
      (syntax-parse c
        [((~literal and/c) cᵢ ...)
         (define clauses (map go (syntax->list #'(cᵢ ...))))
         (and (andmap values clauses) (and* clauses))]
        [((~literal or/c) cᵢ ...)
         (define clauses (map go (syntax->list #'(cᵢ ...))))
         (and (andmap values clauses) (or* clauses))]
        [((~literal not/c) d)
         (define clause (go #'d))
         (and clause (not* clause))]
        [((~literal cons/c) c₁ c₂)
         (define e₀ (go #'pair?))
         (define e₁ (and e₀ (gen-base-guard #'c₁ #`(car #,x))))
         (define e₂ (and e₁ (gen-base-guard #'c₂ #`(cdr #,x))))
         (and e₂ (and* (list e₀ e₁ e₂)))]
        [((~literal listof) _) #f]
        [((~literal list/c) _ ...) #f]
        [((~or (~literal =/c)
               (~literal >/c) (~literal >=/c)
               (~literal </c) (~literal <=/c))
          _)
         #`(real? #,x)]
        [_:number #`(number? #,x)]
        [_:symbol #`(symbol? #,x)]
        [(~literal any/c) #'#t]
        [(~literal none/c) #'#f]
        [c:id (and (base-predicate? #'c) #`(#,(pred-for-TR #'c) #,x))])))

  ;; Generate primitve body when all preconds have passed
  (define/contract (gen-ok-case) (-> (listof syntax?))
    (define/syntax-parse sig:ff (-sig))
    (define dom-init (attribute sig.init))
    (define dom-rest (attribute sig.rest))
    (define rng (attribute sig.rng))
    (define/with-syntax (W ...) (-Wₙ))
    (define/with-syntax (s ...) (-sₙ))
    (define/with-syntax (b ...) (-bₙ))
    (define n (length dom-init))
    (define base-guard-init
      (and (-lift?)
           (let ([clauses (map gen-base-guard dom-init (-bₙ))])
             (and (andmap values clauses) (and* clauses)))))

    (cond
      ;; Generate predicates differently
      [(and (identifier? rng) (free-identifier=? #'boolean? rng))
       (hack:make-available (-o) implement-predicate)
       (list #`(implement-predicate (-Σ-σ #,(-Σ)) #,(-Γ) '#,(-o) #,(-Ws)))]
      [dom-rest
       (define/with-syntax (concrete-case-clauses ...)
         (cond
           [(and base-guard-init (range-is-base? rng))
            (define/with-syntax mk-bₐ #`(-b (apply #,(-o) #,@(-bₙ) #,(-b*))))
            (define base-guard
              (syntax-parse dom-rest
                [(~or (~literal list?) ((~literal listof) (~literal any/c)))
                 base-guard-init]
                [((~literal listof) c*)
                 (define base-guard-rest
                   (syntax-parse #'c*
                     [(~or p:id #|hack b/c of TR|# ((~literal and/c) p:id _ ...))
                      #`(andmap #,(pred-for-TR #'p) #,(-b*))]
                     [_
                      (define body (gen-base-guard #'c* #'x))
                      (and body
                           #`(andmap (λ ([x : Base]) #,body) #,(-b*)))]))
                 (and base-guard-rest (and* (list base-guard-init base-guard-rest)))]))
            (hack:make-available (-o) ts->bs)
            (list #`[((-b b) ... (app ts->bs #,(-b*))) #:when (and #,(-b*) #,base-guard)
                     (define bₐ mk-bₐ)
                     {set (-ΓA #,(-Γ) (-W (list bₐ) bₐ))}])]
           [else '()]))
       (define/with-syntax (symbolic-case-clauses ...)
         (list #`[(s ... #,(-s*)) #,@(gen-sym-case)]))
       (list #`(match* ((-W¹-t W) ... (map -W¹-t #,(-W*)))
                 concrete-case-clauses ...
                 symbolic-case-clauses ...))]
      [else
       (define/with-syntax (concrete-case-clauses ...)
         (cond
           [(and base-guard-init (range-is-base? rng))
            (define/with-syntax mk-bₐ
              (syntax-parse (-o)
                [(~literal any/c) #'-tt]
                [(~literal none/c) #'-ff]
                [o #`(-b (o #,@(-bₙ)))]))
            (list #`[((-b b) ...) #:when #,base-guard-init
                     (define bₐ mk-bₐ)
                     {set (-ΓA #,(-Γ) (-W (list bₐ) bₐ))}])]
           [else '()]))
       (define/with-syntax (symbolic-case-clauses ...)
         (list #`[(s ...) #,@(gen-sym-case)]))
       (list
        #`(match* ((-W¹-t W) ...)
            concrete-case-clauses ...
            symbolic-case-clauses ...))]))

  ;; Generate function that refines results when more is known about arguments
  (define/contract (gen-refine-body V)
    (identifier? . -> . (listof syntax?))

    (define/contract (gen-check-definitely W c)
      (identifier? syntax? . -> . syntax?)
      (define (pos?->R pos?) (if pos? #''✓ #''✗))
      (let go ([c c] [pos? #t])
        (define/with-syntax R (pos?->R pos?))
        (hack:make-available (-o) ⊢?/quick)
        (syntax-parse c
          [((~literal and/c) c* ...)
           (and* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
          [((~literal or/c ) c* ...)
           (or* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
          [((~literal not/c) d) (go #'d (not pos?))]
          [((~literal cons/c) c₁ c₂)
           (and* (list #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) -cons? #,W)
                       (go #'c₁ pos?)
                       (go #'c₂ pos?)))]
          [((~literal listof) _)
           (raise-syntax-error
            'def-prim
            (format "~a: `listof` in refinement not supported for now" #''o)
            c)]
          [((~literal list/c) c* ...)
           (go (desugar-list/c (syntax->list #'(c* ...))))]
          [((~literal =/c ) x) #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) '=  #,W (-W¹ (-b x) (-b x)))]
          [((~literal >/c ) x) #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) '>  #,W (-W¹ (-b x) (-b x)))]
          [((~literal >=/c) x) #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) '>= #,W (-W¹ (-b x) (-b x)))]
          [((~literal </c ) x) #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) '<  #,W (-W¹ (-b x) (-b x)))]
          [((~literal <=/c) x) #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) '<= #,W (-W¹ (-b x) (-b x)))]
          [(~literal any/c) #'#t]
          [(~literal none/c) #'#f]
          [x:lit #'(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) 'equal? #,W (-W¹ (-b x) (-b x)))]
          [c:id #`(⊢?/quick R (-Σ-σ #,(-Σ)) #,(-Γ) 'c #,W)])))

    (define/syntax-parse ctc:ff (-sig))

    `(,@(for/list ([refinement (in-list (-refs))])
          (define/syntax-parse ref:ff refinement)
          (define ref-init (attribute ref.init))
          (define ref-rest (attribute ref.rest))
          (define ref-rng  (attribute ref.rng))
          (define precond-init (map gen-check-definitely (-Wₙ) ref-init))
          (define precond-rest
            (syntax-parse ref-rest
              [(~or (~literal list?) ((~literal listof) (~literal any/c)) #f)
               (list #'#t)]
              [((~literal listof) c*)
               (list #`(for/and : Boolean ([Wᵢ (in-list #,(-W*))])
                         #,(gen-check-definitely #'Wᵢ #'c*)))]))
          (define precond (and* (append precond-init precond-rest)))
          (hack:make-available (-o) V+)
          #`(when #,precond
              #,@(for/list ([cᵣ (in-list (rng->refinement ref-rng))])
                   #`(set! #,V (V+ (-Σ-σ #,(-Σ)) #,V #,cᵣ)))))
      ,V))

  ;; Generate primitive body for the case where 1+ argument is symbolic
  ;; Free variable `Γ` available as "the" path condition
  (define/contract (gen-sym-case) (-> (listof syntax?))

    (define/syntax-parse sig:ff (-sig))
    (define/syntax-parse rng:rngc (attribute sig.rng))
    (define dom-rest (attribute sig.rest))

    ;; List of possible refinement sets to result according to contract range
    (define/contract refinement-sets (listof (listof syntax?))
      (match (attribute rng.values)
        [(list d)
         (let go ([c d])
           (syntax-parse c
             [((~literal and/c) c* ...)
              (let go/and/c ([cs (syntax->list #'(c* ...))])
                (match cs
                  ['() (list (list))]
                  [(cons c cs*)
                   (remove-duplicates
                    (for/list ([ref-set₁ (in-list (go c))]
                               [ref-set₂ (in-list (go/and/c cs*))])
                      (remove-duplicates (append ref-set₁ ref-set₂))))]))]
             [((~literal or/c) cᵢ ...)
              (append-map go (syntax->list #'(cᵢ ...)))]
             [((~literal not/c) d)
              (cond [(identifier? #'d) (list (list #'(-not/c 'd)))]
                    [else (raise-syntax-error
                           'def-prim
                           (format "~a: only identifier can follow not/c in range" (-o))
                           c)])]
             [((~literal cons/c) _ _)
              (raise-syntax-error
               'def-prim
               (format "~a: `cons/c` in range not supported for now" (syntax-e (-o)))
               c)]
             [((~literal listof) _)
              (raise-syntax-error
               'def-prim
               (format "~a: `listof` in range not supported for now" (syntax-e (-o)))
               c)]
             [((~literal list/c) c* ...)
              (go (desugar-list/c (syntax->list #'(c* ...))))]
             [((~literal =/c) x) (list (list #''real? #'(-≡/c x)))]
             [((~literal >/c) x) (list (list #''real? #'(->/c x)))]
             [((~literal >=/c) x) (list (list #''real? #'(-≥/c x)))]
             [((~literal </c) x) (list (list #''real? #'(-</c x)))]
             [((~literal <=/c) x) (list (list #''real? #'(-≤/c x)))]
             [x:lit (list (list #'(-≡/c x)))]
             [(~literal any/c) (list (list))]
             [(~literal none/c) (list)]
             [c:id {list (list #''c)}]))]
        [rngs
         (raise-syntax-error
          'def-prim
          "TODO: multiple returns"
          rngs)]))

    (define (refs->V refs)
      (foldr (λ (ref V)
               (define/with-syntax p
                 (syntax-parse ref
                   [((~literal quote) c:id) (hack:resolve-alias #'c)]
                   [p #'p]))
               (hack:make-available (-o) V+)
               #`(V+ (-Σ-σ #,(-Σ)) #,V p))
             (with-hack:make-available ((-o) +●)
               #'(+●))
             refs))

    (define/with-syntax mk-sₐ
      (cond [(-volatile?) #'#f]
            [dom-rest
             (hack:make-available (-o) ?t@)
             #`(apply ?t@ '#,(-o) #,@(-sₙ) #,(-s*))]
            [else
             (hack:make-available (-o) ?t@)
             #`(?t@ '#,(-o) #,@(-sₙ))]))

    (cond
      [(null? (-refs))
       (list #`(define sₐ mk-sₐ)
             #`(set #,@(for/list ([refs (in-list refinement-sets)])
                         #`(-ΓA #,(-Γ) (-W (list #,(refs->V refs)) sₐ)))))]
      [else
       (define/with-syntax o.refine (format-id #f "~a.refine" (syntax-e (-o))))
       (list #`(define sₐ mk-sₐ)
             #`(define (o.refine [V : -V]) #,@(gen-refine-body #'V))
             #`(set #,@(for/list ([refs (in-list refinement-sets)])
                         #`(-ΓA #,(-Γ) (-W (list (o.refine #,(refs->V refs))) sₐ)))))]))

  ;; Generate full precondition check
  (define/contract (gen-precond-checks body)
    ((listof syntax?) . -> . (listof syntax?))

    (define on-done/c (syntax? boolean? . -> . symbol?))
    (define push/c (symbol? (or/c syntax? (listof syntax?)) . -> . symbol?))

    ;; Generate precondition check before executing `κ`
    (define/contract (gen-precond-check! W c κ push-thunk!)
      (identifier? syntax? symbol? push/c . -> . symbol?)

      (define gen-name!
        (let ([i 0]
              [infix (syntax-e W)])
          (λ ([prefix 'chk])
            (begin0 (format-symbol "~a-~a-~a" prefix infix i)
              (set! i (add1 i))))))

      (define-values (local-thunks push-local-thunk!) (new-thunk-table))

      (define/contract (gen-listof-check! c pos? on-done push-thunk!)
        (syntax? boolean? on-done/c push/c . -> . symbol?)
        
        (define/contract (gen-loop-body! c pos?)
          (syntax? boolean? . -> . (listof syntax?))
          ;; These are real "thunks" with no parameter
          (define-values (listof.thunks listof.push!) (new-thunk-table))

          (define/contract (go! c pos? on-done)
            (syntax? boolean? (syntax? boolean? . -> . symbol?) . -> . symbol?)
            (syntax-parse c
              [((~literal and/c) c* ... cₙ)
               (foldr
                (λ (cᵢ κ)
                  (go! cᵢ pos?
                       (λ (c pos*?)
                         (if (equal? pos*? pos?) κ (on-done c pos*?)))))
                (go! #'cₙ pos? on-done)
                (syntax->list #'(c* ...)))]
              [((~literal or/c) c* ... cₙ)
               (foldr
                (λ (cᵢ κ)
                  (go! cᵢ pos?
                       (λ (c pos*?)
                         (if (equal? pos*? pos?) (on-done c pos?) κ))))
                (go! #'cₙ pos? on-done)
                (syntax->list #'(c* ...)))]
              [((~literal not/c) c*)
               (go! #'c* (not pos?) on-done)]
              [((~literal cons/c) c₁ c₂)
               (error "TODO")]
              [((~literal listof) c*)
               (error "TODO")]
              [((~literal list/c) c* ...)
               (go! (desugar-list/c (syntax->list #'(c* ...))) pos? on-done)]
              [((~literal =/c) x:real)
               (error "TODO")]
              [((~literal </c) x:real)
               (error "TODO")]
              [((~literal <=/c) x:real)
               (error "TODO")]
              [((~literal >/c) x:real)
               (error "TODO")]
              [((~literal >=/c) x:real)
               (error "TODO")]
              [x:lit
               (error "TODO")]
              [c:id
               (define/with-syntax p (hack:resolve-alias #'c))
               (hack:make-available (-o) p∋Vs/handler)
               (listof.push!
                (gen-name! 'chk-V-elem)
                #`(p∋Vs/handler
                     #,(on-done #'c pos?)
                     #,(on-done #'c (not pos?))
                     (-Σ-σ #,(-Σ)) p Vₕ))]))

          (define κ₀ (go! c pos?
                          (λ (c pos?)
                            (cond [pos? 'chk-tail]
                                  [else (listof.push!
                                         (gen-name! 'fail)
                                         ((-gen-blm) #`(-blm (ℓ-src (-ℒ-app #,(-ℒ))) '#,(-o) (list '#,c) (list Vₕ) (-ℒ-app #,(-ℒ)))))]))))
          (for/fold ([acc (hash-ref listof.thunks κ₀)])
                    ([(f es) (in-hash listof.thunks)] #:unless (equal? f κ₀))
            (cons #`(define (#,(->id f)) #,@es) acc)))

        (hack:make-available (-o) σ@)
        (define body
          (list #`(define-set seen-tails : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
                #`(define cache : (HashTable ⟪α⟫ (℘ -ΓA)) (make-hasheq))
                #`(define result (delay (#,κ #,(-Γ))))
                #`(let go : (℘ -ΓA) ([V : -V (-W¹-V #,W)])
                    (match V
                      [(-Cons αₕ αₜ)
                       (define (chk-tail)
                         (cond [(seen-tails-has? αₜ) (force result)]
                               [else
                                (seen-tails-add! αₜ)
                                (hash-ref!
                                 cache αₜ
                                 (λ ()
                                   (for/union : (℘ -ΓA) ([Vₜ (in-set (σ@ #,(-Σ) αₜ))])
                                              (go Vₜ))))]))
                       (define (chk-elem)
                         (for/union : (℘ -ΓA) ([Vₕ (in-set (σ@ #,(-Σ) αₕ))])
                           #,@(gen-loop-body! c pos?)))
                       (chk-elem)]
                      [(-b (list)) (force result)]
                      [(-● ps)
                       (cond
                         [(∋ ps 'list?) (force result)]
                         [else #,((-gen-blm) #`(-blm (ℓ-src (-ℒ-app #,(-ℒ))) '#,(-o) '(list?) (list V) (-ℒ-app #,(-ℒ))))])]
                      [_ #,((-gen-blm) #`(-blm (ℓ-src (-ℒ-app #,(-ℒ))) '#,(-o) '(list?) (list V) (-ℒ-app #,(-ℒ))))]))))
        (push-thunk! (gen-name! 'chk-listof) body))

      (define/contract (go! c pos? on-done)
        (syntax? boolean? on-done/c . -> . symbol?)

        (define/contract (gen-comp/c-case x ★ ★/c)
          (syntax? identifier? identifier? . -> . symbol?)
          (define why (if pos? #`(#,★/c #,x) #`(-not/c (#,★/c #,x))))
          (hack:make-available (-o) Γ+/-oW/handler)
          (push-local-thunk!
           (gen-name!)
           (list #`(define bₓ (-b #,x))
                 #`(Γ+/-oW/handler
                    #,(->id (on-done why pos?))
                    #,(->id (on-done why (not pos?)))
                    (-Σ-σ #,(-Σ)) #,(-Γ) '#,★ #,W (-W¹ bₓ bₓ)))))

        (syntax-parse c
          ;; For function contracts, generate first-order checks only
          [c:hf
           (define/with-syntax arity
             (match (attribute c.arity)
               [(? integer? n) n]
               [(arity-at-least n) #`(arity-at-least #,n)]))
           (define/with-syntax c-msg
             (format-symbol "arity-includes/c ~a" (syntax-e #'arity)))
           (hack:make-available (-o) arity-check/handler)
           (define κ₁
             (push-local-thunk!
              (gen-name!)
              #`(arity-check/handler
                 #,(->id (on-done #''c-msg pos?))
                 #,(->id (on-done #''c-msg (not pos?)))
                 #,(-Γ)
                 #,W
                 arity)))
           (hack:make-available (-o) Γ+/-oW/handler)
           (push-local-thunk!
            (gen-name!)
            #`(Γ+/-oW/handler
               #,(->id κ₁)
               #,(->id (on-done #''procedure? (not pos?)))
               (-Σ-σ #,(-Σ)) #,(-Γ) 'procedure? #,W))]

          [((~literal and/c) c* ... cₙ)
           (foldr
            (λ (c κ)
              (go! c pos?
                   (λ (c pos*?)
                     (if (equal? pos*? pos?) κ (on-done c pos*?)))))
            (go! #'cₙ pos? on-done)
            (syntax->list #'(c* ...)))]
          [((~literal or/c) c* ... cₙ)
           (foldr
            (λ (c κ)
              (go! c pos?
                   (λ (c pos*?)
                     (if (equal? pos*? pos?) (on-done c pos?) κ))))
            (go! #'cₙ pos? on-done)
            (syntax->list #'(c* ...)))]
          [((~literal not/c) c*)
           (go! #'c* (not pos?) on-done)]
          [((~literal cons/c) c₁ c₂)
           (go! #'cons? pos?
                (λ (c pos*?)
                  (cond
                    [(equal? pos*? pos?)
                     ;; TODO inefficient
                     (define/with-syntax W₁ (format-id W "~a.car" (syntax-e W)))
                     (define/with-syntax W₂ (format-id W "~a.cdr" (syntax-e W)))
                     (define-values (thunks* push*!) (new-thunk-table))
                     (define κₙ (on-done c pos?))
                     (define κ₂ (gen-precond-check! #'W₂ #'c₂ κₙ push*!))
                     (define κ₁ (gen-precond-check! #'W₁ #'c₁ κ₂ push*!))
                     (hack:make-available #'c₁ unchecked-ac)
                     (push-local-thunk!
                      (gen-name! 'chk-cons/c)
                      #`(for/union : (℘ -ΓA) ([W₁ (in-set (unchecked-ac (-Σ-σ #,(-Σ)) #,(-Γ) -car #,W))]
                                              [W₂ (in-set (unchecked-ac (-Σ-σ #,(-Σ)) #,(-Γ) -cdr #,W))])
                                   #,@(gen-program κ₁ thunks*)))]
                    [else (on-done c pos*?)])))]
          [((~literal listof) c*)
           (go! #'null? pos?
                (λ (c pos*?)
                  (cond
                    [(equal? pos*? pos?)
                      (on-done c pos?)]
                    [else
                     (go! #'cons? pos?
                          (λ (c pos*?)
                            (cond [(equal? pos*? pos?)
                                   (gen-listof-check! #'c* pos? on-done push-local-thunk!)]
                                  [else (on-done c pos*?)])))])))]
          [((~literal list/c) c* ...)
           (go! (desugar-list/c (syntax->list #'(c* ...))) pos? on-done)]
          [((~literal =/c ) x) (gen-comp/c-case #'x #'=  #'-≡/c)]
          [((~literal </c ) x) (gen-comp/c-case #'x #'<  #'-</c)]
          [((~literal <=/c) x) (gen-comp/c-case #'x #'<= #'-≤/c)]
          [((~literal >/c ) x) (gen-comp/c-case #'x #'>  #'->/c)]
          [((~literal >=/c) x) (gen-comp/c-case #'x #'>= #'-≥/c)]
          [x:lit
           (define why (if pos? #'(-≡/c x) #'(-≢/c x)))
           (hack:make-available (-o) Γ+/-oW/handler)
           (push-local-thunk!
            (gen-name!)
            (list #'(define bₓ (-b x))
                  #`(Γ+/-oW/handler
                     #,(->id (on-done why pos?))
                     #,(->id (on-done why (not pos?)))
                     (-Σ-σ #,(-Σ)) #,(-Γ) 'equal? #,W (-W¹ bₓ bₓ))))]
          [(~literal any/c) (on-done #''any/c pos?)]
          [(~literal none/c) (on-done #'not/c (not pos?))]
          [c:id
           (define/with-syntax p (hack:resolve-alias #'c))
           (define why (if pos? #''c #'(-not/c 'c)))
           (hack:make-available (-o) Γ+/-oW/handler)
           (push-local-thunk!
            (gen-name!)
            #`(Γ+/-oW/handler
               #,(->id (on-done why pos?))
               #,(->id (on-done why (not pos?)))
               (-Σ-σ #,(-Σ)) #,(-Γ) p #,W))]))

      (define entry-name
        (go! c #t
             (λ (c pos?)
               (if pos?
                   κ
                   (push-local-thunk!
                    (gen-name! 'blm)
                    ((-gen-blm) #`(-blm (ℓ-src (-ℒ-app #,(-ℒ))) '#,(-o) (list #,c) (list (-W¹-V #,W)) (-ℒ-app #,(-ℒ)))))))))
      
      (cond [(hash-ref local-thunks entry-name #f) =>
             (λ (entry)
               (define name (format-symbol "check-~a" (syntax-e W)))
               (define body
                 `(,@(for/list ([(f es) (in-hash local-thunks)]
                                #:unless (equal? f entry-name))
                       #`(define (#,(->id f) [#,(-Γ) : -Γ]) #,@es))
                   ,@entry))
               (push-thunk! name body))]
            [else κ]))

    (define/contract (gen-chk-rest! κ push-thunk!)
      (symbol? (symbol? (or/c syntax? (listof syntax?)) . -> . symbol?) . -> . symbol?)
      (define/syntax-parse sig:ff (-sig))
      (syntax-parse (attribute sig.rest)
        [(~or (~literal list?) ((~literal listof) (~literal any/c))) κ]
        [((~literal listof) c)
         (define-values (local-thunks push-local-thunk!) (new-thunk-table))
         (push-local-thunk! 'chk-rst #`(loop #,(-W*) #,(-Γ)))
         (define κ* (gen-precond-check! #'Wₕ #'c 'chk-rst push-local-thunk!))
         (define/with-syntax (body ...) (gen-program κ* local-thunks))
         (push-thunk!
          (format-symbol "chk-~a" (syntax-e (-W*)))
          #`(let loop : (℘ -ΓA) ([#,(-W*) : (Listof -W¹) #,(-W*)] [#,(-Γ) : -Γ #,(-Γ)])
                 (match #,(-W*)
                   ['() (#,κ #,(-Γ))]
                   [(cons Wₕ #,(-W*)) body ...])))]))

    (define-values (thunks push-thunk!) (new-thunk-table))
    (push-thunk! 'run-body body)
    (syntax-parse (-sig)
      [((~literal ->) cₓ ... cₐ)
       (define/contract (step! W c κ)
         (identifier? syntax? symbol? . -> . symbol?)
         (gen-precond-check! W c κ push-thunk!))
       (gen-program (foldr step! 'run-body (-Wₙ) (syntax->list #'(cₓ ...))) thunks)]
      [((~literal ->*) (cₓ ...) #:rest cᵣ cₐ)
       (define κ* (gen-chk-rest! 'run-body push-thunk!))
       (define/contract (step! W c κ)
         (identifier? syntax? symbol? . -> . symbol?)
         (gen-precond-check! W c κ push-thunk!))
       (gen-program (foldr step! κ* (-Wₙ) (syntax->list #'(cₓ ...))) thunks)]))

  (define/contract (gen-arity-check n body)
    (procedure-arity? (listof syntax?) . -> . (listof syntax?))
    
    (match n
      [(? integer? n)
       (list
        #`(match #,(-Ws)
            [(list #,@(-Wₙ))
             #,@body]
            [_
             #,((-gen-blm)
                (with-hack:make-available ((-o) blm-arity)
                  #`(blm-arity (-ℒ-app #,(-ℒ)) '#,(-o) #,n (map -W¹-V #,(-Ws)))))]))]
      [(arity-at-least 0)
       (list* #`(define #,(-W*) #,(-Ws))
              body)]
      [(arity-at-least n)
       (list
        #`(match #,(-Ws)
            [(list* #,@(-Wₙ) #,(-W*))
             #,@body]
            [_
             #,((-gen-blm)
                (with-hack:make-available ((-o) blm-arity)
                  #`(blm-arity (-ℒ-app #,(-ℒ)) '#,(-o) (arity-at-least #,n) (map -W¹-V #,(-Ws)))))]))])))
