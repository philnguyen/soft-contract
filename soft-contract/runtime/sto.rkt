#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "../utils/set.rkt" "definition.rkt")

(: σ@/list : -σ (Listof -α) → (℘ (Listof -V)))
;; Look up store at addresses. Return all possible combinations
(define (σ@/list σ αs)
  (match αs
    [(cons α αs*)
     (define Vs (σ@ σ α))
     (define Vss (σ@/list σ αs*))
     (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
       (cons V Vs))]
    ['() {set '()}]))
