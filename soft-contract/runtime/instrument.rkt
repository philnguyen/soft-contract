#lang typed/racket/base

(provide (all-defined-out))

(require racket/list
         syntax/parse/define
         "../utils/main.rkt"
         "definition.rkt")

(define call-count : (HashTable -⟦e⟧! Integer) (make-hasheq))
(define total-time : (HashTable -⟦e⟧! Integer) (make-hasheq))

(define-simple-macro (λ/instrument (x ...) e ...)
  (instrument (λ (x ...) e ...)))

(define/memoeq (instrument [⟦e⟧ : -⟦e⟧!]) : -⟦e⟧!
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define t₀ (current-milliseconds))
    (define ans (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧))
    (define δt (- (current-milliseconds) t₀))
    (hash-update! call-count ⟦e⟧ add1 (λ () 0))
    (hash-update! total-time ⟦e⟧ (λ ([t : Integer]) (+ t δt)) (λ () 0))
    ans))

(: table-max ((HashTable -⟦e⟧! Integer) Natural → (Listof (Pairof -⟦e⟧! Integer))))
(define (table-max m num)
  (define sorted-pairs
    (sort
     (hash->list m)
     (λ ([p₁ : (Pairof -⟦e⟧! Integer)] [p₂ : (Pairof -⟦e⟧! Integer)])
       (> (cdr p₁) (cdr p₂)))))
  (take sorted-pairs (min (hash-count m) num)))

(: best-count ([] [Natural] . ->* . (Listof (Pairof -⟦e⟧! Integer))))
(define (best-count [num 1]) (table-max call-count num))
(: best-total ([] [Natural] . ->* . (Listof (Pairof -⟦e⟧! Integer))))
(define (best-total [num 1]) (table-max total-time num))
