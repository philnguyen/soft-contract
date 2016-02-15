#lang typed/racket/base

(provide (all-defined-out))

(require "../ast/definition.rkt" "runtime.rkt")

(: ⟦-ℰ.if⟧ : -⟦e⟧ -⟦e⟧ → -⟦ℰ⟧)
(define (((⟦-ℰ.if⟧ ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ρ Γ 𝒳)
  (define-values (δσ₀ As₀ ℋs₀) (⟦e₀⟧ M σ ρ Γ 𝒳))
  (error "TODO"))

(: ⟦-ℰ.@⟧ : (Listof -W¹) (Listof -⟦e⟧) -src-loc → -⟦ℰ⟧)
(define (((⟦-ℰ.@⟧ Ws ⟦e⟧s loc) ⟦e⟧) M σ ρ Γ 𝒳)
  (define-values (δσ As ℋs) (⟦e⟧ M σ ρ Γ 𝒳))
  (error "TODO"))
