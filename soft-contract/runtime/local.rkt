#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "definition.rkt")

(: -ℒ-with-Γ : -ℒ -Γ → -ℒ)
(define (-ℒ-with-Γ ℒ Γ)
  (cond [(eq? Γ (-ℒ-cnd ℒ)) ℒ] ; common case, keep old instance
        [else (match-define (-ℒ ρ _ 𝒞) ℒ)
              (-ℒ ρ Γ 𝒞)]))

(: -ℒ-with-ρ : -ℒ -ρ → -ℒ)
(define (-ℒ-with-ρ ℒ ρ)
  (cond [(eq? ρ (-ℒ-env ℒ)) ℒ]
        [else (match-define (-ℒ _ Γ 𝒞) ℒ)
              (-ℒ ρ Γ 𝒞)]))
