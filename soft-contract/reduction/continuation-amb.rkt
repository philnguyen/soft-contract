#lang typed/racket/base

(provide ↝.amb)

(require racket/match
         "../utils/function.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "helpers.rkt")

(: ↝.amb : (Listof -⟦e⟧) → -⟦e⟧)
(define (↝.amb ⟦e⟧s)
  (λ (M σ X ℒ)
    (for*/ans ([⟦e⟧ ⟦e⟧s]) (⟦e⟧ M σ X ℒ))))
