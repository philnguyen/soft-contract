#lang typed/racket/base

(provide approx@)

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         typed/racket/unit
         racket/splicing
         unreachable
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit approx@
  (import evl^ val^
          prover^)
  (export approx^)
  (init-depend val^)

  (: collapse-R^-1 : (U Σ Σᵥ) R^ → (Values T^ Φ^))
  (define (collapse-R^-1 Σ R^)
    (define ?retain (retainable-symbols (map/set R-_0 R^) 1))
    (match (?retain 0)
      [(? values S) (values S (set-union-map R-_1 R^))]
      [_ (for/fold ([T* : V^ ∅] [Φ^* : Φ^ ∅]) ([Rᵢ (in-set R^)])
           (match-define (R (list Tᵢ) Φ^ᵢ) Rᵢ)
           (values (∪ T* (T->V Σ Φ^ᵢ Tᵢ)) (∪ Φ^* Φ^ᵢ)))])) 

  (: collapse-value-lists : (U Σ Σᵥ) R^ Natural → R)
  (define (collapse-value-lists Σ Rs n)
    (define ?retain (retainable-symbols (map/set R-_0 Rs) n))
    (define W-vec : (Vectorof T^) (make-vector n ∅))
    (define-set Φs : Φ)
    (for ([Rᵢ (in-set Rs)])
      (match-define (R Wᵢ Φ^ᵢ) Rᵢ)
      (set! Φs ((iter-⊔ Φ^⊔) Φs Φ^ᵢ))
      (for ([Tₖ (in-list Wᵢ)] [k (in-range n)])
        (define Tₖ*
          (match (?retain k)
            [(? values S) S]
            [else (∪ (assert (vector-ref W-vec k) set?) (T->V Σ Φ^ᵢ Tₖ))]))
        (vector-set! W-vec k Tₖ*)))
    (R (vector->list W-vec) Φs))

  (: R⊕ : (U Σ Σᵥ) R R → R)
  (define (R⊕ Σ R₁ R₂)
    (: W⊕ : Φ^ W W → W)
    (define (W⊕ Φ^ W₁ W₂)
      (for/list ([T₁ (in-list W₁)] [T₂ (in-list W₂)])
        (cond [(or (set? T₁) (set? T₂) (not (equal? T₁ T₂)))
               (∪ (T->V Σ Φ^ T₁) (T->V Σ Φ^ T₂))]
              [else T₁])))
    
    (match-define (R W₁ Φ^₁) R₁)
    (match-define (R W₂ Φ^₂) R₂)
    (define Φ^* ((iter-⊔ Φ^⊔) Φ^₁ Φ^₂))
    (R (W⊕ Φ^* W₁ W₂) Φ^*))

  (: retainable-symbols ([W^] [Integer] . ->* . (Integer → (Option S))))
  (define (retainable-symbols Ws [n (apply max ((inst set-map W Index) Ws length))])
    (define vals : (Vectorof (Option S)) (make-vector n 'untouched))
    (for ([W (in-set Ws)])
      (for ([Tᵢ (in-list W)] [i (in-naturals)])
        (cond [(set? Tᵢ) (vector-set! vals i #f)]
              [else (match (vector-ref vals i)
                      ['untouched (vector-set! vals i Tᵢ)]
                      [(== Tᵢ) (void)]
                      [_ (vector-set! vals i #f)])])))
    (λ (i) (vector-ref vals i)))

  (: ⊔ᵥ : Σᵥ α (U V V^) → Σᵥ)
  (define (⊔ᵥ Σ α V)
    (hash-update Σ α (λ ([V₀ : V^])
                       (if (set? V) ((iter-⊔ V^⊔) V₀ V) (V^⊔ V₀ V)))
                 mk-∅))

  (: ⊔ₖ : Σₖ αₖ Ξ:co → Σₖ)
  (define (⊔ₖ Σ α Ξ)
    (hash-update Σ α (λ ([Ξs : (℘ Ξ:co)]) (Ξ^⊔ Ξs Ξ)) mk-∅))

  (: ⊔ₐ : Σₐ Ξ:co (U R R^) → Σₐ)
  (define (⊔ₐ Σ Ξ R)
    (hash-update Σ Ξ (λ ([R₀ : R^])
                       (if (set? R) ((iter-⊔ R^⊔) R₀ R) (R^⊔ R₀ R))
                       ) mk-∅))

  (: ⊔ᵥ! : Σ α (U V V^) → Void)
  (define (⊔ᵥ! Σ α V) (set-Σ-val! Σ (⊔ᵥ (Σ-val Σ) α V)))

  (: ⊔T! : Σ Φ^ α (U T T^) → Void)
  (define (⊔T! Σ Φ^ α T) (⊔ᵥ! Σ α (T->V Σ Φ^ T)))

  (: ⊔T*! : Σ Φ^ (Listof α) (Listof T^) → Void)
  (define (⊔T*! Σ Φ^ αs Ts)
    (for ([α (in-list αs)] [T (in-list Ts)])
      (⊔T! Σ Φ^ α T)))

  (: ⊔ᵥ*! : Σ (Listof α) (Listof V^) → Void)
  (define (⊔ᵥ*! Σ αs Vs)
    (for ([α (in-list αs)] [V (in-list Vs)])
      (⊔ᵥ! Σ α V)))

  (: ⊔ₐ! : Σ Ξ:co (U R R^) → Void)
  (define (⊔ₐ! Σ Ξ R) (set-Σ-evl! Σ (⊔ₐ (Σ-evl Σ) Ξ R)))
  
  (: ⊔ₖ! : Σ αₖ Ξ:co → Void)
  (define (⊔ₖ! Σ αₖ Ξ) (set-Σ-kon! Σ (⊔ₖ (Σ-kon Σ) αₖ Ξ))) 

  ;; FIXME: could have avoided this if all fields on the stack are allocated
  (define cmp-Ξ : (?Cmp Ξ:co)
    (match-lambda**
     [((Ξ:co K₁ m H) (Ξ:co K₂ m H)) (cmp-K K₁ K₂)]
     [(_ _) #f]))

  (define cmp-K : (?Cmp K)
    (match-lambda**
     [((K Fs₁ α) (K Fs₂ α)) (fold-cmp cmp-F Fs₁ Fs₂)]
     [(_ _) #f]))

  (define cmp-F : (?Cmp F)
    (match-lambda** 
     [((F:Ap Ts₁ Es₁ ℓ) (F:Ap Ts₂ Es₂ ℓ))
      (Ord:* (fold-cmp cmp-T^ Ts₁ Ts₂) (fold-cmp cmp-EΡ Es₁ Es₂))]
     [((F:Let ℓ xs bnds bnds₁ E Ρ) (F:Let ℓ xs bnds bnds₂ E Ρ))
      (fold-cmp cmp-bnd bnds₁ bnds₂)]
     [((F:Bgn0:E W^₁ Es Ρ) (F:Bgn0:E W^₂ Es Ρ))
      (cmp-sets W^₁ W^₂)]
     [((F:Mon:C Ctx x₁) (F:Mon:C Ctx x₂))
      (cmp-EΡ x₁ x₂)]
     [((F:Mon:V Ctx x₁) (F:Mon:V Ctx x₂))
      (cmp-EΡ x₁ x₂)]
     [((F:Mon* Ctx W₁ W₂ ℓs W₃) (F:Mon* Ctx W₄ W₅ ℓs W₆))
      (Ord:* (cmp-W W₁ W₄)
             (cmp-W W₂ W₅)
             (cmp-W W₃ W₆))]
     [((F:==>:Dom W₁ Es ?E E Ρ ℓ) (F:==>:Dom W₂ Es ?E E Ρ ℓ))
      (cmp-W W₁ W₂)]
     [((F:==>:Rst W₁ E Ρ ℓ) (F:==>:Rst W₂ E Ρ ℓ))
      (cmp-W W₁ W₂)]
     [((F:==>:Rng W₁ T₁ ℓ) (F:==>:Rng W₂ T₂ ℓ))
      (Ord:* (cmp-W W₁ W₂)
             (or (and (equal? T₁ T₂) '=)
                 (and T₁ T₂ (cmp-T^ T₁ T₂))))]
     [((F:St/C ℓ 𝒾 W₁ Es Ρ) (F:St/C ℓ 𝒾 W₂ Es Ρ))
      (cmp-W W₁ W₂)]
     [((F:Mon-Or/C Ctx T₁ T₂ T₃) (F:Mon-Or/C Ctx T₄ T₅ T₆))
      (Ord:* (cmp-T^ T₁ T₄)
             (cmp-T^ T₂ T₅)
             (cmp-T^ T₃ T₆))]
     [((F:If:Flat/C T₁ blms₁) (F:If:Flat/C T₂ blms₂))
      (Ord:* (cmp-T^ T₁ T₂) (cmp-sets blms₁ blms₂))]
     [((F:Fc-Or/C α αℓ T₁) (F:Fc-Or/C α αℓ T₂))
      (cmp-T^ T₁ T₂)]
     [((F:Fc-Not/C T₁) (F:Fc-Not/C T₂))
      (cmp-T^ T₁ T₂)]
     [((F:Fc-Struct/C ℓ 𝒾 W₁ Es) (F:Fc-Struct/C ℓ 𝒾 W₂ Es))
      (cmp-W W₁ W₂)]
     [((F:Fc:C ℓ T₁) (F:Fc:C ℓ T₂))
      (cmp-T^ T₁ T₂)]
     [(F₁ F₂) (and (equal? F₁ F₂) '=)]))

  (define cmp-bnd : (?Cmp (Pairof Symbol T^))
    (match-lambda**
     [((cons x T₁) (cons x T₂)) (cmp-T^ T₁ T₂)]
     [(_ _) #f]))

  (define cmp-EΡ : (?Cmp (U EΡ T^))
    (match-lambda**
     [((? T^? T₁) (? T^? T₂)) (cmp-T^ T₁ T₂)]
     [(x x) '=]
     [(_ _) #f]))

  (: V^⊔ : V^ V → V^)
  (define (V^⊔ Vs Vᵢ) (set-add Vs Vᵢ))

  (define (cmp-W [W₁ : W] [W₂ : W]) (fold-cmp cmp-T^ W₁ W₂))
  (define cmp-T^ (cmp-T^/$ #f #f))
  (define Ξ^⊔ (compact-with ((inst join-by-max Ξ:co) cmp-Ξ))) 
  )

