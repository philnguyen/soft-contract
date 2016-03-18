#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "definition.rkt")

(: -ℬ-with-Γ : -ℬ -Γ → -ℬ)
(define (-ℬ-with-Γ ℬ Γ)
  (cond [(eq? Γ (-ℬ-cnd ℬ)) ℬ] ; common case, keep old instance
        [else (match-define (-ℬ ⟦e⟧ ρ _ 𝒞) ℬ)
              (-ℬ ⟦e⟧ ρ Γ 𝒞)]))

(: -ℬ-with-ρ : -ℬ -ρ → -ℬ)
(define (-ℬ-with-ρ ℬ ρ)
  (cond [(eq? ρ (-ℬ-env ℬ)) ℬ]
        [else (match-define (-ℬ ⟦e⟧ _ Γ 𝒞) ℬ)
              (-ℬ ⟦e⟧ ρ Γ 𝒞)]))
