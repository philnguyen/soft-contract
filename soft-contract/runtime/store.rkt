#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "../utils/map.rkt" "addr.rkt" "val.rkt")

;; store maps addresses to values
(define-type -σ (MMap -α -V))
(define -σ⊥ : -σ (hash))
(define-type -Δσ (ΔMap -α -V))

(: σ@ : -σ -α → (Setof -V))
;; Look up the store for all values at given address
(define (σ@ σ α) (hash-ref σ α))

(: σ@₁ : -σ -α → -V)
;; Look up the store for a single value at given address
(define (σ@₁ σ α)
  (define Vs (hash-ref σ α))
  (cond
    [(= 1 (set-count Vs)) (set-first Vs)]
    [else (error 'Internal "expect exactly 1 value at address ~a, given ~a"
                 α (set-count Vs))]))

(: σ@/list : -σ (Listof -α) → (Setof (Listof -V)))
;; Look up store, return every possible list of values
(define (σ@/list σ αs)
  (match αs
    ['() {set (list)}]
    [(cons α βs)
     (define Vss (σ@/list σ βs))
     (for*/set: : (Setof (Listof -V)) ([V (σ@ σ α)] [Vs Vss])
       (cons V Vs))]))

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) (in-hash σ)])
    `(,(show-α α) ↦ ,@(for/list : (Listof Sexp) ([V Vs]) (show-V V)))))
