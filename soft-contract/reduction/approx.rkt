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
    (hash-update Σ α (λ ([V₀ : V^]) (if (set? V) (V⊔ V₀ V) (V⊔₁ V₀ V))) mk-∅))

  (: ⊔ₖ : Σₖ αₖ Ξ:co → Σₖ)
  (define (⊔ₖ Σ α Ξ)
    (hash-update Σ α (λ ([Ξs : (℘ Ξ:co)]) (Ξ^⊔ Ξs Ξ)) mk-∅))

  (: ⊔ₐ : Σₐ Ξ:co (U R R^) → Σₐ)
  (define (⊔ₐ Σ Ξ R)
    (hash-update Σ Ξ (λ ([R₀ : R^]) (if (set? R) ((iter-⊔ R^⊔) R₀ R) (R^⊔ R₀ R))) mk-∅))

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
  (define Ξ⊔ : (Joiner Ξ:co)
    (match-lambda**
     [((Ξ:co K₁ m H) (Ξ:co K₂ m H)) (with-guard ([K (K⊔ K₁ K₂)])
                                      (Ξ:co K m H))]
     [(_ _) #f]))

  (define K⊔ : (Joiner K)
    (match-lambda**
     [((K Fs₁ α) (K Fs₂ α)) (with-guard ([Fs (?map F⊔ Fs₁ Fs₂)])
                              (K Fs α))]
     [(_ _) #f]))

  (define F⊔ : (Joiner F)
    (match-lambda**
     [(F₁ F₂) #:when (equal? F₁ F₂) F₁]
     [((F:Ap Ts₁ Es₁ ℓ) (F:Ap Ts₂ Es₂ ℓ))
      (with-guard ([Ts (?map T⊔ Ts₁ Ts₂)]
                   [Es (?map EΡ⊔ Es₁ Es₂)])
        (F:Ap Ts Es ℓ))]
     [((F:Let ℓ xs bnds bnds₁ E Ρ) (F:Let ℓ xs bnds bnds₂ E Ρ))
      (with-guard ([bnds* (?map bnd⊔ bnds₁ bnds₂)])
        (F:Let ℓ xs bnds bnds* E Ρ))]
     [((F:Bgn0:E W^₁ Es Ρ) (F:Bgn0:E W^₂ Es Ρ))
      (with-guard ([W^* (W^⊔ W^₁ W^₂)])
        (F:Bgn0:E W^* Es Ρ))]
     [((F:Mon:C Ctx x₁) (F:Mon:C Ctx x₂))
      (with-guard ([x (EΡ⊔ x₁ x₂)])
        (F:Mon:C Ctx x))]
     [((F:Mon:V Ctx x₁) (F:Mon:V Ctx x₂))
      (with-guard ([x (EΡ⊔ x₁ x₂)])
        (F:Mon:V Ctx x))]
     [((F:Mon* Ctx W₁ W₂ ℓs W₃) (F:Mon* Ctx W₄ W₅ ℓs W₆))
      (with-guard ([W₁* (W⊔ W₁ W₄)]
                   [W₂* (W⊔ W₂ W₅)]
                   [W₃* (W⊔ W₃ W₆)])
        (F:Mon* Ctx W₁* W₂* ℓs W₃*))]
     [((F:==>:Dom W₁ Es ?E E Ρ ℓ) (F:==>:Dom W₂ Es ?E E Ρ ℓ))
      (with-guard ([W* (W⊔ W₁ W₂)])
        (F:==>:Dom W* Es ?E E Ρ ℓ))]
     [((F:==>:Rst W₁ E Ρ ℓ) (F:==>:Rst W₂ E Ρ ℓ))
      (with-guard ([W (W⊔ W₁ W₂)])
        (F:==>:Rst W E Ρ ℓ))]
     [((F:==>:Rng W₁ T₁ ℓ) (F:==>:Rng W₂ T₂ ℓ))
      (with-guard ([W (W⊔ W₁ W₂)])
        (or (and (equal? T₁ T₂) (F:==>:Rng W T₁ ℓ))
            (and T₁ T₂ (with-guard ([T (T⊔ T₁ T₂)])
                         (F:==>:Rng W T ℓ)))))]
     [((F:St/C ℓ 𝒾 W₁ Es Ρ) (F:St/C ℓ 𝒾 W₂ Es Ρ))
      (with-guard ([W (W⊔ W₁ W₂)])
        (F:St/C ℓ 𝒾 W Es Ρ))]
     [((F:Mon-Or/C Ctx T₁ T₂ T₃) (F:Mon-Or/C Ctx T₄ T₅ T₆))
      (with-guard ([T₁* (T⊔ T₁ T₄)]
                   [T₂* (T⊔ T₂ T₅)]
                   [T₃* (T⊔ T₃ T₆)])
        (F:Mon-Or/C Ctx T₁* T₂* T₃*))]
     [((F:If:Flat/C T₁ blms₁) (F:If:Flat/C T₂ blms₂))
      (with-guard ([T (T⊔ T₁ T₂)])
        (F:If:Flat/C T (∪ blms₁ blms₂)))]
     [((F:Fc-Or/C α αℓ T₁) (F:Fc-Or/C α αℓ T₂))
      (with-guard ([T (T⊔ T₁ T₂)])
        (F:Fc-Or/C α αℓ T))]
     [((F:Fc-Not/C T₁) (F:Fc-Not/C T₂))
      (with-guard ([T (T⊔ T₁ T₂)])
        (F:Fc-Not/C T))]
     [((F:Fc-Struct/C ℓ 𝒾 W₁ Es) (F:Fc-Struct/C ℓ 𝒾 W₂ Es))
      (with-guard ([W (W⊔ W₁ W₂)])
        (F:Fc-Struct/C ℓ 𝒾 W Es))]
     [((F:Fc:C ℓ T₁) (F:Fc:C ℓ T₂))
      (with-guard ([T (T⊔ T₁ T₂)])
        (F:Fc:C ℓ T))]
     [(_ _) #f]))

  (define bnd⊔ : (Joiner (Pairof Symbol T^))
    (match-lambda**
     [((cons x T₁) (cons x T₂)) (with-guard ([T (T⊔ T₁ T₂)]) (cons x T))]))

  (define EΡ⊔ : (Joiner (U EΡ T^))
    (match-lambda**
     [((? T^? T₁) (? T^? T₂)) (T⊔ T₁ T₂)]
     [(x y) #:when (equal? x y) x]
     [(_ _) #f]))

  (define W^⊔ : (Joiner W^)
    (λ (W^₁ W^₂)
      (or (and (⊆ W^₁ W^₂) W^₂)
          (and (⊆ W^₂ W^₁) W^₁))))

  (define W⊔ : (Joiner W)
    (match-lambda**
     [((cons T₁ W₁) (cons T₂ W₂))
      (with-guard ([T (T⊔ T₁ T₂)]
                   [W (W⊔ W₁ W₂)])
        (cons T W))]
     [('() '()) '()]
     [(_ _) #f]))

  (define T⊔ : (Joiner T^)
    (match-lambda**
     [(x x) x]
     [((? set? s₁) (? set? s₂)) (or (and (⊆ s₁ s₂) s₂)
                                    (and (⊆ s₂ s₁) s₁))]
     [((? V? V) (? set? s)) #:when (∋ s V) s]
     [((? set? s) (? V? V)) #:when (∋ s V) s]
     [(_ _) #f]))

  (define Ξ^⊔ (compact-with Ξ⊔))
  )
