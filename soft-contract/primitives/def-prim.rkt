#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
;; TODO:
;; - [ ] listof
;; - [ ] multiple valued return
;; - [ ] #:other-errors
;; - [ ] limited dependent contract to specify `vector-ref`
;;      , or actually just def/custom it if there are only few cases
(provide (all-defined-out))

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
         "../utils/set.rkt"
         "../utils/map.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "def-prim-runtime.rkt")

(begin-for-syntax

  (define/contract (gen-program entry table)
    (symbol? (hash/c symbol? (listof syntax?)) . -> . (listof syntax?))
    (for/fold ([acc (hash-ref table entry)])
              ([(f es) (in-hash table)] #:unless (equal? f entry))
      (cons #`(define (#,(->id f) [#,(-Γ) : -Γ]) #,@es) acc)))
  
  ;; Global parameters that need to be set up for each `def-prim`
  (define-parameter/contract
    ; identifiers available to function body
    [-Σ identifier? #f]
    [-Γ identifier? #f]
    [-σ identifier? #f]
    [-M identifier? #f]
    [-ℓ identifier? #f]
    [-l identifier? #f]
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
    [-lift? boolean? #f])

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
    (define/syntax-parse sig:sig (-sig))
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
       (list #`(implement-predicate #,(-M) #,(-σ) #,(-Γ) '#,(-o) #,(-Ws)))]
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
            (list #`[((-b b) ... (app ss->bs #,(-b*))) #:when (and #,(-b*) #,base-guard)
                     (define bₐ mk-bₐ)
                     {set (-ΓA #,(-Γ) (-W (list bₐ) bₐ))}])]
           [else '()]))
       (define/with-syntax (symbolic-case-clauses ...)
         (list #`[(s ... #,(-s*)) #,@(gen-sym-case)]))
       (list #`(match* ((-W¹-s W) ... (map -W¹-s #,(-W*)))
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
        #`(match* ((-W¹-s W) ...)
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
        (syntax-parse c
          [((~literal and/c) c* ...)
           (and* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
          [((~literal or/c ) c* ...)
           (or* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
          [((~literal not/c) d) (go #'d (not pos?))]
          [((~literal cons/c) c₁ c₂)
           (and* (list #`(⊢?/quick R #,(-σ) #,(-Γ) -cons? #,W)
                       (go #'c₁ pos?)
                       (go #'c₂ pos?)))]
          [((~literal listof) _)
           (raise-syntax-error
            'def-prim
            (format "~a: `listof` in refinement not supported for now" #''o)
            c)]
          [((~literal list/c) c* ...)
           (go (desugar-list/c (syntax->list #'(c* ...))))]
          [((~literal =/c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '=  #,W (-W¹ (-b x) (-b x)))]
          [((~literal >/c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '>  #,W (-W¹ (-b x) (-b x)))]
          [((~literal >=/c) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '>= #,W (-W¹ (-b x) (-b x)))]
          [((~literal </c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '<  #,W (-W¹ (-b x) (-b x)))]
          [((~literal <=/c) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '<= #,W (-W¹ (-b x) (-b x)))]
          [(~literal any/c) #'#t]
          [(~literal none/c) #'#f]
          [x:lit #'(⊢?/quick R #,(-σ) #,(-Γ) 'equal? #,W (-W¹ (-b x) (-b x)))]
          [c:id #`(⊢?/quick R #,(-σ) #,(-Γ) 'c #,W)])))

    (define/syntax-parse ctc:sig (-sig))

    `(,@(for/list ([refinement (in-list (-refs))])
          (define/syntax-parse ref:sig refinement)
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
          #`(when #,precond
              #,@(for/list ([cᵣ (in-list (rng->refinement ref-rng))])
                   #`(set! #,V (V+ σ #,V #,cᵣ)))))
      ,V))

  ;; Generate primitive body for the case where 1+ argument is symbolic
  ;; Free variable `Γ` available as "the" path condition
  (define/contract (gen-sym-case) (-> (listof syntax?))

    (define/syntax-parse sig:sig (-sig))
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
             [((~literal =/c) x) (list (list #''real? #'(-=/c x)))]
             [((~literal >/c) x) (list (list #''real? #'(->/c x)))]
             [((~literal >=/c) x) (list (list #''real? #'(-≥/c x)))]
             [((~literal </c) x) (list (list #''real? #'(-</c x)))]
             [((~literal <=/c) x) (list (list #''real? #'(-≤/c x)))]
             [x:lit (list (list #'(-≡/c (-b x))))]
             [(~literal any/c) (list (list))]
             [(~literal none/c) (list)]
             [c:id {list (list #''c)}]))]
        [rngs
         (raise-syntax-error
          'def-prim
          "TODO: multiple returns"
          rngs)]))

    (define (refs->V  refs) (if (null? refs) #'-●/V        #`(-● {set #,@refs})))
    (define (refs->Vs refs) (if (null? refs) #'-●/Vs #`(list (-● {set #,@refs}))))

    (define/with-syntax mk-sₐ
      (cond [dom-rest #`(apply -?@ '#,(-o) #,@(-sₙ) #,(-s*))]
            [else #`(-?@ '#,(-o) #,@(-sₙ))]))

    (cond
      [(null? (-refs))
       (list #`(define sₐ mk-sₐ)
             #`(set #,@(for/list ([refs (in-list refinement-sets)])
                         #`(-ΓA #,(-Γ) (-W #,(refs->Vs refs) sₐ)))))]
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
               (listof.push!
                (gen-name! 'chk-V-elem)
                #`(with-p∋Vs (σ 'c Vₕ)
                    #:on-t #,(on-done #'c pos?)
                    #:on-f #,(on-done #'c (not pos?))))]))

          (define κ₀ (go! c pos?
                          (λ (c pos?)
                            (cond [pos? 'chk-tail]
                                  [else (listof.push!
                                         (gen-name! 'fail)
                                         #`{set (-ΓA #,(-Γ) (-blm #,(-l) '#,(-o) (list '#,c) (list Vₕ)))})]))))
          (for/fold ([acc (hash-ref listof.thunks κ₀)])
                    ([(f es) (in-hash listof.thunks)] #:unless (equal? f κ₀))
            (cons #`(define (#,(->id f)) #,@es) acc)))
        
        (define body
          (list #`(define-set seen-tails : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
                #`(define cache : (HashTable -⟪α⟫ (℘ -ΓA)) (make-hasheq))
                #`(define result : (Promise (℘ -ΓA)) (delay (#,κ #,(-Γ))))
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
                                   (for/union : (℘ -ΓA) ([Vₜ (in-set (σ@ σ αₜ))])
                                              (go Vₜ))))]))
                       (define (chk-elem)
                         (for/union : (℘ -ΓA) ([Vₕ (in-set (σ@ σ αₕ))])
                           #,@(gen-loop-body! c pos?)))
                       (chk-elem)]
                      [(-b (list)) (force result)]
                      [(-● ps) #|TODO|# (blm #,(-Γ) #,(-l) '#,(-o) 'list? V)]
                      [_ (blm #,(-Γ) #,(-l) '#,(-o) 'list? V)]))))
        (push-thunk! (gen-name! 'chk-listof) body))


      (define/contract (go! c pos? on-done)
        (syntax? boolean? on-done/c . -> . symbol?)

        (define/contract (gen-comp/c-case x ★ ★/c)
          (syntax? identifier? identifier? . -> . symbol?)
          (define why (if pos? #`(#,★/c #,x) #`(-not/c (#,★/c #,x))))
          (push-local-thunk!
           (gen-name!)
           (list #`(define bₓ (-b #,x))
                 #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) '#,★ #,W (-W¹ bₓ bₓ))
                     #:on-t #,(->id (on-done why pos?))
                     #:on-f #,(->id (on-done why (not pos?)))))))

        (syntax-parse c
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
                     (push-local-thunk!
                      (gen-name! 'chk-cons/c)
                      #`(for/union : (℘ -ΓA) ([W₁ (in-set (unchecked-ac #,(-σ) #,(-Γ) -car #,W))]
                                              [W₂ (in-set (unchecked-ac #,(-σ) #,(-Γ) -cdr #,W))])
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
          [((~literal =/c ) x) (gen-comp/c-case #'x #'=  #'-=/c)]
          [((~literal </c ) x) (gen-comp/c-case #'x #'<  #'-</c)]
          [((~literal <=/c) x) (gen-comp/c-case #'x #'<= #'-≤/c)]
          [((~literal >/c ) x) (gen-comp/c-case #'x #'>  #'->/c)]
          [((~literal >=/c) x) (gen-comp/c-case #'x #'>= #'-≥/c)]
          [x:lit
           (define why (if pos? #'(-≡/c bₓ) #'(-not/c (-≡/c bₓ))))
           (push-local-thunk!
            (gen-name!)
            (list #'(define bₓ (-b x))
                  #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) 'equal? #,W (-W¹ bₓ bₓ))
                      #:on-t #,(->id (on-done why pos?))
                      #:on-f #,(->id (on-done why (not pos?))))))]
          [(~literal any/c) (on-done #''any/c pos?)]
          [(~literal none/c) (on-done #'not/c (not pos?))]
          [c:id
           (define/with-syntax p ;; TODO tmp hack
             (syntax-parse #'c
               [(~or (~literal cons?) (~literal pair?)) #'-cons?]
               [(~or (~literal box?)) #'-box?]
               [p:id #''p]))
           (define why (if pos? #''c #'(-not/c 'c)))
           (push-local-thunk!
            (gen-name!)
            #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) p #,W)
                #:on-t #,(->id (on-done why pos?))
                #:on-f #,(->id (on-done why (not pos?)))))]))

      (define entry-name
        (go! c #t
             (λ (c pos?)
               (if pos?
                   κ
                   (push-local-thunk! (gen-name! 'blm) #`(blm #,(-Γ) #,(-l) '#,(-o) #,c #,W))))))
      
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
      (define/syntax-parse sig:sig (-sig))
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
                 (match W*
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

  (define/contract (gen-arity-check body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:sig (-sig))
    
    (match (attribute sig.arity)
      [(? integer? n)
       (list
        #`(match #,(-Ws)
            [(list #,@(-Wₙ))
             (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
             #,@body]
            [_ {set (-ΓA #,(-Γ) (blm-arity #,(-l) '#,(-o) #,n (map -W¹-V #,(-Ws))))}]))]
      [(arity-at-least 0)
       (list* #`(define #,(-W*) #,(-Ws))
              #`(match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
              body)]
      [(arity-at-least n)
       (list
        #`(match #,(-Ws)
            [(list* #,@(-Wₙ) #,(-W*))
             (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
             #,@body]
            [_ {set (-ΓA #,(-Γ) (blm-arity #,(-l)
                                           '#,(-o)
                                           (arity-at-least #,n)
                                           (map -W¹-V #,(-Ws))))}]))])))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Main stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-parser def-const
  [(_ x:id)
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define .x (-b x))
       (hash-set-once! const-table 'x .x))])

(define-syntax (def-prim stx)
  (syntax-parse stx
    ;; Generate total predicates specially to reduce code duplicate
    [(_ o:id ((~literal ->) c:id ... (~literal boolean?)))
     #:when (for/and ([c (in-list (syntax->list #'(c ...)))])
              (free-identifier=? c #'any/c))
     (define n (length (syntax->list #'(c ...))))
     (define/with-syntax .o (prefix-id #'o))
     #`(begin
         (define .o ((total-pred #,n) 'o))
         (hash-set! prim-table 'o .o)
         (set-range! 'o 'boolean?)
         (update-arity! 'o #,n))]

    [(_ o:id sig:sig
        (~optional (~seq #:other-errors [cₑ:fc ...] ...)
                   #:defaults ([(cₑ 2) null]))
        (~optional (~seq #:refinements ref:sig ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))
     
     (check-arity! stx)

     (define n (length (attribute sig.init)))
     (define arity (attribute sig.arity))
     (define/with-syntax .o (prefix-id #'o))
     (define/with-syntax defn-o
       (parameterize ([-o #'o]
                      [-⟪ℋ⟫ #'⟪ℋ⟫]
                      [-ℓ #'ℓ]
                      [-l #'l]
                      [-Σ #'Σ]
                      [-σ #'σ]
                      [-M #'M]
                      [-Γ #'Γ]
                      [-Ws #'Ws]
                      [-Wₙ (gen-ids #'W 'W n)]
                      [-sₙ (gen-ids #'s 's n)]
                      [-bₙ (gen-ids #'b 'b n)]
                      [-W* (format-id #'W* "W*")]
                      [-b* (format-id #'b* "b*")]
                      [-s* (format-id #'s* "s*")]
                      [-sig #'sig]
                      [-lift? (syntax-e #'lift?)]
                      [-refs (syntax->list #'(ref ...))]
                      #;[-errs (syntax->list #'((cₑ ...) ...))])
         #`(define (.o #,(-⟪ℋ⟫) #,(-ℓ) #,(-l) #,(-Σ) #,(-Γ) #,(-Ws))
             #,@(gen-arity-check
                 (gen-precond-checks
                  (gen-ok-case))))))
     ;(pretty-write (syntax->datum #'defn-o))
     #`(begin
         (: .o : -⟦o⟧!)
         defn-o
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))
         (update-arity!
          'o
          #,(match arity
              [(arity-at-least n) #`(arity-at-least #,n)]
              [(? integer? n) n]))
         #,@(syntax-parse #|FIXME|# #'cₐ
              [(~or ((~literal and/c) d:id _ ...) d:id)
               (list #'(set-range! 'o 'd))]
              [_ '()]))]))

;; TODO remove code duplicate
(define-syntax-parser def-prim/custom
  [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id)
      #:domain ([W:id c:fc] ...)
      e:expr ...)
   (define n (length (syntax->list #'(c ...))))
   (define/with-syntax .o (prefix-id #'o))
   (define/with-syntax defn-o
     #`(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
         #,@(parameterize ([-o #'o]
                           [-⟪ℋ⟫ #'⟪ℋ⟫]
                           [-ℓ #'ℓ]
                           [-l #'l]
                           [-Σ #'Σ]
                           [-σ #'σ]
                           [-M #'M]
                           [-Γ #'Γ]
                           [-Ws #'Ws]
                           [-Wₙ (syntax->list #'(W ...))]
                           [-sₙ (gen-ids #'s 's n)]
                           [-bₙ (gen-ids #'b 'b n)]
                           [-W* (format-id #'W* "W*")]
                           [-b* (format-id #'b* "b*")]
                           [-s* (format-id #'s* "s*")]
                           [-sig #'(-> c ... any/c)]
                           #;[-errs (syntax->list #'((cₑ ...) ...))])
              (gen-arity-check
               (gen-precond-checks
                (syntax->list #'(e ...)))))))
   #`(begin
       (: .o : -⟦o⟧!)
       defn-o
       (hash-set! prim-table 'o .o)
       (hash-set! debug-table 'o '#,(syntax->datum #'defn-o)))]
  [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id) e:expr ...)
   (define/with-syntax .o (prefix-id #'o))
   (define/with-syntax defn-o #'(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws) e ...))
   #`(begin
       (: .o : -⟦o⟧!)
       defn-o
       (hash-set! prim-table 'o .o)
       (hash-set! debug-table 'o '#,(syntax->datum #'defn)))])

(define-simple-macro (def-prim/todo x:id clauses ...)
  (def-prim/custom (x ⟪ℋ⟫ ℓ l Σ Γ Ws)
    (error 'x "TODO")))

(define-simple-macro (def-prims (o:id ... (~optional (~seq #:todo o*:id ...)
                                                     #:defaults ([(o* 1) '()])))
                       clauses ...)
  (begin
    (def-prim o clauses ...) ...
    (def-prim/todo o* clauses ...) ...))

(define-simple-macro (def-pred p:id (~optional (dom:fc ...)
                                               #:defaults ([(dom 1) (list #'any/c)])))
  (def-prim p (dom ... . -> . boolean?)))

(define-simple-macro (def-preds (p:id ... (~optional (~seq #:todo q:id ...)
                                                     #:defaults ([(q 1) '()])))
                       rst ...)
  (begin
    (def-pred p rst ...) ...
    (def-pred/todo q rst ...) ...))

(define-simple-macro (def-pred/todo p:id (~optional (dom:fc ...)
                                                    #:defaults ([(dom 1) (list #'any/c)])) ...)
  (def-prim/todo p (dom ... . -> . boolean?)))

(define-syntax-parser def-alias
  [(_ x:id y:id)
   #'(hash-set-once! alias-table 'x 'y)])

(define-syntax-parser def-alias-internal
  [(_ x:id v:id)
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define .x v)
       (hash-set-once! alias-internal-table 'x v))])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (define/with-syntax (r ...) (datum->syntax #f (rng->refinement #'c)))
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define x (-● (set r ...)))
       (hash-set-once! opq-table 'x x))])

(define-syntax-parser dec-implications
  [(_ [p:id (~literal ⇒) q:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define/with-syntax (p ⇒ q ...) clause)
        (for/list ([q (in-list (syntax->list #'(q ...)))])
          #`(add-implication! 'p '#,q)))
      (syntax->list #'([p ⇒ q ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-exclusions
  [(_ [p:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define ps (syntax->list clause))
        (let go ([ps ps] [acc '()])
          (match ps
            [(list) acc]
            [(cons p ps*)
             (go ps*
                 (foldr (λ (p* acc) (cons #`(add-exclusion! '#,p '#,p*) acc)) acc ps*))])))
      (syntax->list #'([p ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-partitions
  [(_ [p:id (q:id ...)] ...)
   (define impl-clauses
     (append-map
      (λ (clause)
        (define/with-syntax (p (q ...)) clause)
        (for/list ([q (in-list (syntax->list #'(q ...)))])
          #`(dec-implications [#,q ⇒ p])))
      (syntax->list #'([p (q ...)] ...))))
   #`(begin
       (dec-exclusions (q ...) ...)
       #,@impl-clauses)])
