#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit val@
  (import pc^ pretty-print^ sto^)
  (export val^)

  (define +● : (-h * → -●)
    (let ([m : (HashTable (Listof -h) -●) (make-hash)])
      (λ hs
        (hash-ref! m hs (λ () (-● (list->set hs)))))))

  (define +W¹ : ([-prim] [-?t] . ->* . -W¹)
    (let ([m : (HashTable -W¹ -W¹) (make-hash)])
      (λ ([b : -prim] [t : -?t b])
        (define W (-W¹ b t))
        (hash-ref! m W (λ () W)))))

  (define +W : ([(Listof -prim)] [-?t] . ->* . -W)
    (let ([m : (HashTable -W -W) (make-hash)])
      (λ ([bs : (Listof -prim)] [t : -?t (apply ?t@ 'values bs)])
        (define W (-W bs t))
        (hash-ref! m W (λ () W)))))

  (define (W¹->W [W : -W¹])
    (match-define (-W¹ V s) W)
    (-W (list V) s))

  (: C-flat? : -V → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? V)
    (match V
      [(-And/C flat? _ _) flat?]
      [(-Or/C flat? _ _) flat?]
      [(? -Not/C?) #t]
      [(? -One-Of/C?) #t]
      [(-St/C flat? _ _) flat?]
      [(or (? -Vectorof?) (? -Vector/C?)) #f]
      [(-Hash/C _ _) #f]
      [(? -=>_?) #f]
      [(or (? -Clo?) (? -Ar?) (? -prim?)) #t]
      [(? -x/C?) #t]
      [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

  (: with-negative-party : -l -V → -V)
  ;; Supply the negative party for blaming
  (define (with-negative-party l V)
    (match V
      [(-Ar C α (-l³ l+ _ lo))
       (-Ar C α (-l³ l+ l lo))]
      [(-St* grd α (-l³ l+ _ lo))
       (-St* grd α (-l³ l+ l lo))]
      [(-Vector/guard grd ⟪α⟫ (-l³ l+ _ lo))
       (-Vector/guard grd ⟪α⟫ (-l³ l+ l lo))]
      [_ V]))

  (: with-positive-party : -l -V → -V)
  (define (with-positive-party l V)
    (match V
      [(-Ar C α (-l³ _ l- lo))
       (-Ar C α (-l³ l l- lo))]
      [(-St* grd α (-l³ _ l- lo))
       (-St* grd α (-l³ l l- lo))]
      [(-Vector/guard grd ⟪α⟫ (-l³ _ l- lo))
       (-Vector/guard grd ⟪α⟫ (-l³ l l- lo))]
      [_ V]))

  (: behavioral? : -σ -V → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? σ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)

    (: check-⟪α⟫! : ⟪α⟫ → Boolean)
    (define (check-⟪α⟫! ⟪α⟫)
      (cond [(seen-has? ⟪α⟫) #f]
            [else
             (seen-add! ⟪α⟫)
             (for/or ([V (σ@ σ ⟪α⟫)])
               (check! V))]))

    (: check! : -V → Boolean)
    (define (check! V)
      (match V
        [(-St _ αs) (ormap check-⟪α⟫! αs)]
        [(-St* _ α _) (check-⟪α⟫! α)]
        [(-Vector αs) (ormap check-⟪α⟫! αs)]
        [(-Vector^ α _) (check-⟪α⟫! α)]
        [(-Ar grd α _) #t]
        [(-=> doms rngs _)
         (match doms
           [(? list? doms)
            (or (for/or : Boolean ([dom (in-list doms)])
                  (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
                (and (pair? rngs)
                     (for/or : Boolean ([rng (in-list rngs)])
                       (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))]
           [(-var doms dom)
            (or (check-⟪α⟫! (-⟪α⟫ℓ-addr dom))
                (for/or : Boolean ([dom (in-list doms)])
                  (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
                (and (pair? rngs)
                     (for/or : Boolean ([rng (in-list rngs)])
                       (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))])]
        [(? -=>i?) #t]
        [(-Case-> cases _)
         (for*/or : Boolean ([kase : (Pairof (Listof ⟪α⟫) ⟪α⟫) cases])
           (match-define (cons doms rng) kase)
           (or (check-⟪α⟫! rng)
               (ormap check-⟪α⟫! doms)))]
        [(or (? -Clo?) (? -Case-Clo?)) #t]
        [_ #f]))

    (check! V))

  (define guard-arity : (-=>_ → Arity)
    (match-lambda
      [(-=> αs _ _) (shape αs)]
      [(and grd (-=>i αs (list mk-D mk-d _) _))
       (match mk-D
         [(-Clo xs _ _ _) (shape xs)]
         [_
          ;; FIXME: may be wrong for var-args. Need to have saved more
          (length αs)])]))

  (: blm-arity : ℓ -l Arity (Listof -V) → -blm)
  (define blm-arity
    (let ([arity->msg : (Arity → Symbol)
                      (match-lambda
                        [(? integer? n)
                         (format-symbol (case n
                                          [(0 1) "~a value"]
                                          [else "~a values"])
                                        n)]
                        [(arity-at-least n)
                         (format-symbol "~a+ values" n)])])
      (λ (ℓ lo arity Vs)
        (-blm (ℓ-src ℓ) lo (list (arity->msg arity)) Vs ℓ))))

  (: strip-C : -V → -edge.tgt)
  (define strip-C
    (match-lambda
      [(-Clo xs ⟦e⟧ _ _) (list 'flat ⟦e⟧)] ; distinct from just ⟦e⟧
      [(-And/C _ (-⟪α⟫ℓ _ ℓ₁) (-⟪α⟫ℓ _ ℓ₂)) (list 'and/c ℓ₁ ℓ₂)]
      [(-Or/C  _ (-⟪α⟫ℓ _ ℓ₁) (-⟪α⟫ℓ _ ℓ₂)) (list  'or/c ℓ₁ ℓ₂)]
      [(-Not/C (-⟪α⟫ℓ _ ℓ)) (list 'not/c ℓ)]
      [(-One-Of/C bs) bs]
      [(-St/C _ (-𝒾 𝒾 _) ⟪α⟫ℓs) (cons 𝒾 (map -⟪α⟫ℓ-loc ⟪α⟫ℓs))]
      [(-Vectorof (-⟪α⟫ℓ _ ℓ)) (list 'vectorof ℓ)]
      [(-Vector/C ⟪α⟫ℓs) (cons 'vector/c (map -⟪α⟫ℓ-loc ⟪α⟫ℓs))]
      [(-Hash/C (-⟪α⟫ℓ _ ℓₖ) (-⟪α⟫ℓ _ ℓᵥ)) (list 'hash/c ℓₖ ℓᵥ)]
      [(-=> _ _ ℓ) (list '-> ℓ)]
      [(-=>i _ _ ℓ) (list '->i ℓ)]
      [(-Case-> _ ℓ) (list 'case-> ℓ)]
      [(-x/C α)
       (match-define (-α.x/c x) (⟪α⟫->-α α))
       (list 'recursive-contract/c x)]
      [(? -o? o) o]
      [(-Ar _ (app ⟪α⟫->-α (-α.fn _ ℓ _ _ _)) _) (list 'flat ℓ)]
      [V (error 'strip-C "~a not expected" V)]))

  (: predicates-of-V : -V → (℘ -h))
  (define predicates-of-V
    (match-lambda
      [(-b (? number?)) {set 'number?}]
      [(-b (? null?)) {set 'null?}]
      [(-Clo _ ⟦e⟧ _ _) {set (-clo ⟦e⟧)}]
      [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _)) #:when 𝒾 {set (-st-p 𝒾)}]
      [(or (? -Ar?) (? -o?)) {set 'procedure?}]
      [_ ∅]))

  )
