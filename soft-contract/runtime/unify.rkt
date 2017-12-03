#lang typed/racket/base

(provide unify@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit unify@
  (import sto^)
  (export unify^)

  (: unify : -σ -δσ -V -V → (Option Bij))
  (define (unify σ δσ V₁ V₂)
    (define-set seen : (Pairof ⟪α⟫ ⟪α⟫) #:as-mutable-hash? #t)

    (: lift (∀ (X) (Bij X X → (Option Bij)) → Bij (Listof X) (Listof X) → (Option Bij)))
    (define ((lift f) bij xs₁ xs₂)
      (for/fold ([bij : (Option Bij) bij])
                ([x₁ (in-list xs₁)]
                 [x₂ (in-list xs₂)]
                 #:break (not bij))
        (f (assert bij) x₁ x₂)))

    (: go-α : Bij ⟪α⟫ ⟪α⟫ → (Option Bij))
    (define (go-α bij α₁ α₂)
      (define k (cons α₁ α₂))
      (cond
        [(seen-has? k) bij]
        [else
         (seen-add! k)
         (for/or : (Option Bij) ([V₁ (in-set (σ@ σ δσ α₁))])
           (for/or : (Option Bij) ([V₂ (in-set (σ@ σ δσ α₂))])
             (go-V bij V₁ V₂)))]))

    (define go-αs : (Bij (Listof ⟪α⟫) (Listof ⟪α⟫) → (Option Bij)) (lift go-α))

    (: go-V : Bij -V -V → (Option Bij))
    (define (go-V bij V₁ V₂)
      (match* (V₁ V₂)
        [((? integer? s₁) (? integer? s₂))
         (Bij-ext bij s₁ s₂)]
        [((-St 𝒾 αs₁) (-St 𝒾 αs₂))
         (go-αs bij αs₁ αs₂)]
        [((-Vector αs₁) (-Vector αs₂))
         (go-αs bij αs₁ αs₂)]
        [((-Vector^ α₁ n) (-Vector^ α₂ n))
         (go-α bij α₁ α₂)]
        [((-Hash^ αₖ₁ αᵥ₁ b?) (-Hash^ αₖ₂ αᵥ₂ b?))
         (go-αs bij (list αₖ₁ αᵥ₁) (list αₖ₂ αᵥ₂))]
        [((-Set^ α₁ b?) (-Set^ α₂ b?))
         (go-α bij α₁ α₂)]
        [((-Clo xs e ρ₁) (-Clo xs e ρ₂))
         (go-ρ bij ρ₁ ρ₂)]
        [((-Case-Clo cases₁) (-Case-Clo cases₂))
         (go-Vs bij cases₁ cases₂)]
        [((-Ar G₁ α₁ ctx) (-Ar G₂ α₂ ctx))
         (match (go-V bij G₁ G₂)
           [(? values bij) (go-α bij α₁ α₂)]
           [#f #f])]
        [((-St* G₁ α₁ ctx) (-St* G₂ α₂ ctx))
         (match (go-V bij G₁ G₂)
           [(? values bij) (go-α bij α₁ α₂)]
           [#f #f])]
        [((-Vector/guard G₁ α₁ ctx) (-Vector/guard G₂ α₂ ctx))
         (match (go-V bij G₁ G₂)
           [(? values bij) (go-α bij α₁ α₂)]
           [#f #f])]
        [((-Hash/guard G₁ α₁ ctx) (-Hash/guard G₂ α₂ ctx))
         (match (go-V bij G₁ G₂)
           [(? values bij) (go-α bij α₁ α₂)]
           [#f #f])]
        [((-Set/guard G₁ α₁ ctx) (-Set/guard G₂ α₂ ctx))
         (match (go-V bij G₁ G₂)
           [(? values bij) (go-α bij α₁ α₂)]
           [#f #f])]
        [((-Sealed α₁) (-Sealed α₂))
         (go-α bij α₁ α₂)]
        [((-And/C f? l₁ r₁) (-And/C f? l₂ r₂))
         (go-αℓs bij (list l₁ r₁) (list l₂ r₂))]
        [((-Or/C f? l₁ r₁) (-Or/C f? l₂ r₂))
         (go-αℓs bij (list l₁ r₁) (list l₂ r₂))]
        [((-Not/C αℓ₁) (-Not/C αℓ₂))
         (go-αℓ bij αℓ₁ αℓ₂)]
        [((-x/C α₁) (-x/C α₂))
         (go-α bij α₁ α₂)]
        [((-=> dom₁ rng₁) (-=> dom₂ rng₂))
         (and (or (and (equal? 'any rng₁) (equal? 'any rng₂))
                  (and (list? rng₁) (list? rng₂) (= (length rng₁) (length rng₂))))
              (match (go-var-αℓ bij dom₁ dom₂)
                [(? values bij)
                 (and (list? rng₁) (list? rng₂) (go-αℓs bij rng₁ rng₂))]
                [#f #f]))]
        [((-=>i dom₁ (cons rng₁ _)) (-=>i dom₂ (cons rng₂ _)))
         (match (go-αℓs bij dom₁ dom₂)
           [(? values bij) (go-V bij rng₁ rng₂)]
           [#f #f])]
        [((-∀/C xs c ρ₁) (-∀/C xs c ρ₂))
         (go-ρ bij ρ₁ ρ₂)]
        [((-Case-> Cs₁) (-Case-> Cs₂))
         (go-Vs bij Cs₁ Cs₂)]
        [((-St/C f? 𝒾 Cs₁) (-St/C f? 𝒾 Cs₂))
         (go-αℓs bij Cs₁ Cs₂)]
        [((-Vectorof αℓ₁) (-Vectorof αℓ₂))
         (go-αℓ bij αℓ₁ αℓ₂)]
        [((-Vector/C αℓs₁) (-Vector/C αℓs₂))
         (go-αℓs bij αℓs₁ αℓs₂)]
        [((-Hash/C k₁ v₁) (-Hash/C k₂ v₂))
         (go-αℓs bij (list k₁ v₁) (list k₂ v₂))]
        [((-Set/C elems₁) (-Set/C elems₂))
         (go-αℓ bij elems₁ elems₂)]
        [(_ _) (and (equal? V₁ V₂) bij)]))

    (define go-Vs : (Bij (Listof -V) (Listof -V) → (Option Bij)) (lift go-V))

    (: go-ρ : Bij -ρ -ρ → (Option Bij))
    (define (go-ρ bij ρ₁ ρ₂)
      (for/fold ([bij : (Option Bij) bij])
                ([(x α₁) (in-hash ρ₁)]
                 #:break (not bij))
        (go-α (assert bij) α₁ (hash-ref ρ₂ x))))

    (: go-var-αℓ : Bij (-maybe-var -⟪α⟫ℓ) (-maybe-var -⟪α⟫ℓ) → (Option Bij))
    (define (go-var-αℓ bij αℓ₁ αℓ₂)
      (match* (αℓ₁ αℓ₂)
        [((? list? l₁) (? list? l₂))
         (and (= (length l₁) (length l₂)) (go-αℓs bij l₁ l₂))]
        [((-var l₁ r₁) (-var l₂ r₂))
         (and (= (length l₁) (length l₂))
              (match (go-αℓs bij l₁ l₂)
                [(? values bij) (go-αℓ bij r₁ r₂)]
                [#f #f]))]))

    (: go-αℓ : Bij -⟪α⟫ℓ -⟪α⟫ℓ → (Option Bij))
    (define (go-αℓ bij αℓ₁ αℓ₂)
      (go-α bij (-⟪α⟫ℓ-addr αℓ₁) (-⟪α⟫ℓ-addr αℓ₂)))

    (define go-αℓs : (Bij (Listof -⟪α⟫ℓ) (Listof -⟪α⟫ℓ) → (Option Bij)) (lift go-αℓ))
    
    (go-V Bij-empty V₁ V₂))
  )
