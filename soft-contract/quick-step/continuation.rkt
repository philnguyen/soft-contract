#lang typed/racket/base

(provide (all-defined-out))

(require "../ast/definition.rkt" "runtime.rkt")

(: ⟦-ℰ.if⟧ : -⟦e⟧ -⟦e⟧ → -⟦ℰ⟧)
(define (((⟦-ℰ.if⟧ ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ℬ)
  (define-values (δσ₀ As₀ ℋs₀) (⟦e₀⟧ M σ ℬ))
  (error "TODO"))

(: ⟦-ℰ.@⟧ : (Listof -WV) (Listof -⟦e⟧) -src-loc → -⟦ℰ⟧)
(define (((⟦-ℰ.@⟧ Wvs ⟦e⟧s loc) ⟦e⟧) M σ ℬ)
  (define-values (δσ As ℋs) (⟦e⟧ M σ ℬ))
  (error "TODO"))
