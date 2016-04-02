#lang typed/racket/base

(provide ↝.wrap.st wrap.vct.hetero)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         "helpers.rkt")

(: ↝.wrap.st : -struct-info (Listof -α) -α.st Mon-Info → -⟦ℰ⟧)
(define ((↝.wrap.st s αs α l³) ⟦e⟧)
  (define muts (-struct-info-mutables s))
  (define αs* : (Listof (Option -α))
    (for/list ([(α i) (in-indexed αs)])
      (and (∋ muts i) α)))
  (define V* (-St* s αs* α l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.wrap.st s αs α l³ ℰ))
      (λ (σ* Γ* W)
        (match-define (-W (list V) v) W) ; only used internally, should be safe
        (values (⊔ ⊥σ α V) {set (-ΓW Γ* (-W (list V*) v))} ∅ ∅)))
     (⟦e⟧ M σ ℒ))))

(: wrap.vct.hetero : Mon-Info -ℓ (Listof -α) -W¹ → -⟦e⟧)
(define (wrap.vct.hetero l³ ℓ αs Wᵥ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (λ (M σ ℒ)
    (match-define (-ℒ _ Γ 𝒞) ℒ)
    (define α (-α.vct ℓ 𝒞))
    (define V* (-Vector/hetero αs α l³))
    (values (⊔ ⊥σ α Vᵥ) {set (-ΓW Γ (-W (list V*) sᵥ))} ∅ ∅)))

(: wrap.vct.homo : Mon-Info -ℓ -α -W¹ → -⟦e⟧)
(define (wrap.vct.homo l³ ℓ γ Wᵥ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (λ (M σ ℒ)
    (match-define (-ℒ _ Γ 𝒞) ℒ)
    (define α (-α.vct ℓ 𝒞))
    (define V* (-Vector/homo γ α l³))
    (values (⊔ ⊥σ α Vᵥ) {set (-ΓW Γ (-W (list V*) sᵥ))} ∅ ∅)))
