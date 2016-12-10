#lang typed/racket

(provide δ!)

(require "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         "../primitives/main.rkt")

(: δ! : -⟪ℋ⟫ -ℓ -l -Σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))
(define (δ! ⟪ℋ⟫ ℓ l Σ Γ o Ws)
  ((hash-ref prim-table o) ⟪ℋ⟫ ℓ l Σ Γ Ws))
