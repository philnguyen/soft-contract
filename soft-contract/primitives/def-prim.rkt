#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
;; TODO:
;; - [ ] list/c
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
         syntax/parse/define
         "../utils/set.rkt"
         "../utils/map.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "def-prim-runtime.rkt")

(begin-for-syntax
  (define (->id κ) (format-id #f "~a" κ))

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

  #;(define/contract (gen-program entry table)
    (symbol? (hash/c symbol? (listof syntax?)) . -> . (listof syntax?))
    (for/fold ([acc (hash-ref table entry)])
              ([(f es) (in-hash table)] #:unless (equal? f entry))
      (cons #`(define (#,(->id f) [#,(-Γ) : -Γ]) #,@es) acc)))

  ;; Generate primitve body when all preconds have passed
  ;; Free variable `Γ` available as "the" path condition
  #;(define/contract (gen-ok-case doms rng refinement-clauses)
    ((listof syntax?) syntax? (listof syntax?) . -> . (listof syntax?))
    (define n (length doms))

    (with-syntax ([(cₓ ...) doms])
      (define/contract (gen-base-guard c x)
        (syntax? syntax? . -> . (or/c syntax? #f))
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
            [((~or (~literal =/c)
                   (~literal >/c) (~literal >=/c)
                   (~literal </c) (~literal <=/c))
              _)
             #`(real? #,x)]
            [_:number #`(number? #,x)]
            [_:symbol #`(symbol? #,x)]
            [(~literal any/c) #'#t]
            [(~literal none/c) #'#f]
            [(~literal integer?) #`(exact-integer? #,x)]
            [c:id (and (base-predicate? #'c) #`(c #,x))])))
      
      (define (simp@ f xs)
        (syntax-parse f
          [(~literal any/c) #'-tt]
          [(~literal none/c) #'-ff]
          [_ #`(-b (#,f #,@xs))]))

      (with-syntax ([(W ...) (-Wₙ n)]
                    [(s ...) (-sₙ n)]
                    [(b ...) (-bₙ n)])
        (syntax-parse #'cₐ ; generate predicates differently
          [(~literal boolean?)
           (list #`(implement-predicate #,(-M) #,(-σ) #,(-Γ) 'o #,(-Ws)))]
          [_
           (define base-guards
             (and (syntax-e #'lift?)
                  (not (skip-base-case-lifting? #'o))
                  (let ([clauses (map gen-base-guard doms (-bₙ n))])
                    (and (andmap values clauses) (and* clauses)))))
           (define lift-concrete-case? (and base-guards (range-is-base? #'cₐ)))
           (list
            #`(match* ((-W¹-s W) ...)
                #,@(cond
                     [lift-concrete-case?
                      (list #`[((-b b) ...) #:when #,base-guards
                               (define bₐ #,(simp@ #'o (-bₙ n)))
                               {set (-ΓA #,(-Γ) (-W (list bₐ) bₐ))}])]
                     [else '()])
                [(s ...) #,@(gen-sym-case n rng refinement-clauses)]))]))))

  ;; Generate function that refines results when more is known about arguments
  #;(define/contract (gen-refine-body V refinements)
    (identifier? (listof syntax?) . -> . (listof syntax?))

    (define-values (refine-dom-list refine-rng-list)
      (for/lists (refine-dom-list refine-rng-list)
                 ([refinement (in-list refinements)])
        (syntax-parse refinement
          [((rₓ ...) rₐ) (values (syntax->list #'(rₓ ...)) #'rₐ)])))
    
    (define n (length (car refine-dom-list)))

    (define (gen-check-definitely W c)
      (define (pos?->R pos?) (if pos? #''✓ #''✗))
      (let go ([c c] [pos? #t])
        
        (with-syntax ([R (pos?->R pos?)])
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
            [((~literal =/c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '=  #,W (-W¹ (-b x) (-b x)))]
            [((~literal >/c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '>  #,W (-W¹ (-b x) (-b x)))]
            [((~literal >=/c) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '>= #,W (-W¹ (-b x) (-b x)))]
            [((~literal </c ) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '<  #,W (-W¹ (-b x) (-b x)))]
            [((~literal <=/c) x) #`(⊢?/quick R #,(-σ) #,(-Γ) '<= #,W (-W¹ (-b x) (-b x)))]
            [(~literal any/c) #'#t]
            [(~literal none/c) #'#f]
            [x:lit #'(⊢?/quick R #,(-σ) #,(-Γ) 'equal? #,W (-W¹ (-b x) (-b x)))]
            [c:id #`(⊢?/quick R #,(-σ) #,(-Γ) 'c #,W)]))))

    `(,@(for/list ([doms (in-list refine-dom-list)]
                   [rng  (in-list refine-rng-list)])
          (define preconds (map gen-check-definitely (-Wₙ n) doms))
          #`(when #,(and* preconds)
              #,@(for/list ([cᵣ (in-list (rng->refinement rng))])
                   #`(set! #,V (V+ σ #,V #,cᵣ)))))
      ,V))

  ;; Generate primitive body for the case where 1+ argument is symbolic
  ;; Free variable `Γ` available as "the" path condition
  #;(define/contract (gen-sym-case n rng refinement-clauses)
    (integer? syntax? (listof syntax?) . -> . (listof syntax?))
    (define/contract refinement-sets (listof (listof syntax?))
      (let go ([c rng])
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
                        (format "~a: only identifier can follow not/c in range" #'o)
                        c)])]
          [((~literal cons/c) _ _)
           (raise-syntax-error
            'def-prim
            (format "~a: `cons/c` in range not supported for now" (syntax-e #'o))
            c)]
          [((~literal listof/c) _)
           (raise-syntax-error
            'def-prim
            (format "~a: `listof` in range not supported for now" (syntax-e #'o))
            c)]
          [((~literal =/c) x) (list (list #''real? #'(-=/c x)))]
          [((~literal >/c) x) (list (list #''real? #'(->/c x)))]
          [((~literal >=/c) x) (list (list #''real? #'(-≥/c x)))]
          [((~literal </c) x) (list (list #''real? #'(-</c x)))]
          [((~literal <=/c) x) (list (list #''real? #'(-≤/c x)))]
          [x:lit (list (list #'(-≡/c (-b x))))]
          [(~literal any/c) (list (list))]
          [(~literal none/c) (list)]
          [c:id {list (list #''c)}])))

    (define (refs->V refs)
      (cond [(null? refs) #'-●/V]
            [else #`(-● {set #,@refs})]))
    (define (refs->Vs refs)
      (cond [(null? refs) #'-●/Vs]
            [else #`(list (-● {set #,@refs}))]))

    (cond
      [(null? refinement-clauses)
       (list #`(define sₐ (-?@ 'o #,@(-sₙ n)))
             #`(set #,@(for/list ([refs (in-list refinement-sets)])
                         #`(-ΓA #,(-Γ) (-W #,(refs->Vs refs) sₐ)))))]
      [else
       (with-syntax ([o.refine (format-id #f "~a.refine" (syntax-e #'o))])
         (list #`(define sₐ (-?@ 'o #,@(-sₙ n)))
               #`(define (o.refine [V : -V])
                   #,@(gen-refine-body #'V refinement-clauses))
               #`(set #,@(for/list ([refs (in-list refinement-sets)])
                           #`(-ΓA #,(-Γ) (-W (list (o.refine #,(refs->V refs))) sₐ))))))]))

  ;; Generate full precondition check
  #;(define/contract (gen-arg-list-check W-ids cs ok-body)
    ((listof identifier?) (listof syntax?) (listof syntax?) . -> . (listof syntax?))

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
          (list #`(define cache : (HashTable -⟪α⟫ (℘ -ΓA)) (make-hasheq))
                #`(let go : (℘ -ΓA) ([V : -V (-W¹-V #,W)])
                    (match V
                      [(-Cons αₕ αₜ)
                       (define (chk-tail)
                         (hash-ref! cache αₜ
                                    (λ ()
                                      (for/union : (℘ -ΓA) ([Vₜ (in-set (σ@ σ αₜ))])
                                         (go Vₜ)))))
                       (define (chk-elem)
                         (for/union : (℘ -ΓA) ([Vₕ (in-set (σ@ σ αₕ))])
                           #,@(gen-loop-body! c pos?)))
                       (chk-elem)]
                      [(-b (list)) (#,κ #,(-Γ))]
                      [(-● ps) #|TODO|# (blm #,(-Γ) #,(-l) '#,(-o) 'list? V)]
                      [_ (blm #,(-Γ) #,(-l) '#,(-o) 'list? V)]))))
        (push-thunk! (gen-name! 'chk-listof) body))


      (define/contract (go! c pos? on-done)
        (syntax? boolean? on-done/c . -> . symbol?)

        (define/contract (gen-comp/c-case x ★ ★/c)
          (syntax? identifier? identifier? . -> . symbol?)
          (with-syntax ([why (if pos? #`(#,★/c #,x) #`(-not/c (#,★/c #,x)))])
            (push-local-thunk!
             (gen-name!)
             (list #`(define bₓ (-b #,x))
                   #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) '#,★ #,W (-W¹ bₓ bₓ))
                       #:on-t #,(->id (on-done #'why pos?))
                       #:on-f #,(->id (on-done #'why (not pos?))))))))

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
                     (with-syntax ([W₁ (format-id W "~a.car" (syntax-e W))]
                                   [W₂ (format-id W "~a.cdr" (syntax-e W))])
                       (define-values (thunks* push*!) (new-thunk-table))
                       (define κₙ (on-done c pos?))
                       (define κ₂ (gen-precond-check! #'W₂ #'c₂ κₙ push*!))
                       (define κ₁ (gen-precond-check! #'W₁ #'c₁ κ₂ push*!))
                       (push-local-thunk!
                        (gen-name! 'chk-cons/c)
                        #`(for/union : (℘ -ΓA) ([W₁ (in-set (unchecked-ac #,(-σ) #,(-Γ) -car #,W))]
                                                [W₂ (in-set (unchecked-ac #,(-σ) #,(-Γ) -cdr #,W))])
                                     #,@(gen-program κ₁ thunks*))))]
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
          [((~literal =/c ) x) (gen-comp/c-case #'x #'=  #'-=/c)]
          [((~literal </c ) x) (gen-comp/c-case #'x #'<  #'-</c)]
          [((~literal <=/c) x) (gen-comp/c-case #'x #'<= #'-≤/c)]
          [((~literal >/c ) x) (gen-comp/c-case #'x #'>  #'->/c)]
          [((~literal >=/c) x) (gen-comp/c-case #'x #'>= #'-≥/c)]
          [x:lit
           (with-syntax ([why (if pos? #'(-≡/c bₓ) #'(-not/c (-≡/c bₓ)))])
             (push-local-thunk!
              (gen-name!)
              (list #'(define bₓ (-b x))
                    #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) 'equal? #,W (-W¹ bₓ bₓ))
                        #:on-t #,(->id (on-done #'why pos?))
                        #:on-f #,(->id (on-done #'why (not pos?)))))))]
          [(~literal any/c) (on-done #''any/c pos?)]
          [(~literal none/c) (on-done #'not/c (not pos?))]
          [c:id
           (with-syntax ([p (syntax-parse #'c ;; TODO tmp hack
                              [(~or (~literal cons?) (~literal pair?)) #'-cons?]
                              [(~or (~literal box?)) #'-box?]
                              [p:id #''p])]
                         [why (if pos? #''c #'(-not/c 'c))])
             (push-local-thunk!
              (gen-name!)
              #`(with-MΓ⊢oW (#,(-M) #,(-σ) #,(-Γ) p #,W)
                  #:on-t #,(->id (on-done #'why pos?))
                  #:on-f #,(->id (on-done #'why (not pos?))))))]))

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

    (let-values ([(thunks push-thunk!) (new-thunk-table)])
        (push-thunk! 'run-body ok-body)
        
        (define/contract (step! W c on-done)
          (identifier? syntax? symbol? . -> . symbol?)
          (gen-precond-check! W c on-done push-thunk!))
        
        (gen-program (foldr step! 'run-body W-ids cs) thunks)))

  (define/contract (gen-arity-check body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:sig (-sig))
    
    (match (attribute sig.arity)
      [(? integer? n)
       (define/with-syntax c
         (format-symbol (case n
                          [(0 1) "~a value"]
                          [else "~a values"])
                        n))
       (list
        #`(match #,(-Ws)
            [(list #,@(-Wₙ))
             (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
             #,@body]
            [_ {set (-ΓA #,(-Γ)
                         (-blm #,(-l) '#,(-o) '(c) (map -W¹-V #,(-Ws))))}]))]
      [(arity-at-least 0)
       (cons #`(match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
             body)]
      [(arity-at-least n)
       (define/with-syntax c (format-symbol "≥~a values" n))
       (list
        #`(match #,(-Ws)
            [(list* #,@(-Wₙ) #,(-W*))
             (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
             #,@body]
            [_ {set (-ΓA #,(-Γ)
                         (-blm #,(-l) '#,(-o) '(c) (map -W¹-V #,(-Ws))))}]))])
    #;(match* ( (-W*))
      [('() (? identifier? W*))
       (list* #`(define #,W* #,(-Ws))
              #`(match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
              body)]
      [(Wᵢs (? identifier? W*))
       (define n (length Wᵢs))
       (define/with-syntax c-arity (format-symbol "arity-at-least ~a" n))
       (list #`(match #,(-Ws)
                 [(list* #,@Wᵢs #,W*)
                  (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
                  #,@body]
                 [_ {set (-ΓA #,(-Γ)
                              (-blm #,(-l) '#,(-o) (list c-arity) (map -W¹-V #,(-Ws))))}]))]
      [(Wᵢs #f)
       (define n (length Wᵢs))
       (define/with-syntax c-arity (format-symbol "~a values" n))
       (list #`(match #,(-Ws)
                 [(list #,@Wᵢs)
                  (match-define (-Σ #,(-σ) _ #,(-M)) #,(-Σ))
                  #,@body]
                 [_ {set (-ΓA #,(-Γ)
                              (-blm #,(-l) '#,(-o) (list c-arity) (map -W¹-V #,(-Ws))))}]))])))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Main stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-parser def-const
  [(_ x:id)
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x (-b x))
         (hash-set-once! const-table 'x .x)))])

(define-syntax (def-prim stx)
  (check-arity! stx)
  (syntax-parse stx
    ;; Generate total predicates specially to reduce code duplicate
    [(_ o:id ((~literal ->) c ... (~literal boolean?)))
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
                      [-refs (syntax->list #'(ref ...))]
                      #;[-errs (syntax->list #'((cₑ ...) ...))])
         #`(define (.o #,(-⟪ℋ⟫) #,(-ℓ) #,(-l) #,(-Σ) #,(-Γ) #,(-Ws))
             #,@(gen-arity-check
                 (list #'(error "TODO"))
                 #;(gen-arg-list-check
                    (-Wₙ n) doms
                    (gen-ok-case doms
                                 #'cₐ
                                 (syntax->list #'(((rₓ ...) rₐ) ...))))))))
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
         #,@(syntax-parse #'cₐ
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
               (list #'(error "TODO"))
               #;(gen-arg-list-check (syntax->list #'(W ...))
                                     (syntax->list #'(c ...))
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
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x v)
         (hash-set-once! alias-internal-table 'x v)))])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (with-syntax ([(r ...) (datum->syntax #f (rng->refinement #'c))]
                 [.x (prefix-id #'x)])
     #'(begin
         (define x (-● (set r ...)))
         (hash-set-once! opq-table 'x x)))])

(define-syntax-parser dec-implications
  [(_ [p:id (~literal ⇒) q:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (with-syntax ([(p ⇒ q ...) clause])
          (for/list ([q (in-list (syntax->list #'(q ...)))])
            #`(add-implication! 'p '#,q))))
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
        (with-syntax ([(p (q ...)) clause])
          (for/list ([q (in-list (syntax->list #'(q ...)))])
            #`(dec-implications [#,q ⇒ p]))))
      (syntax->list #'([p (q ...)] ...))))
   #`(begin
       (dec-exclusions (q ...) ...)
       #,@impl-clauses)])
