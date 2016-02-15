#lang typed/racket/base

(provide (all-defined-out))

(require racket/set racket/match "../ast/definition.rkt" "addr.rkt")

;; environment maps variable names to addresses
(define-type -ρ (HashTable Symbol -α.x))
(define -ρ⊥ : -ρ (hasheq))

(: ρ↓ : -ρ (Setof Symbol) → -ρ)
;; Restrict environment's domain to given variable names
(define (ρ↓ ρ xs)
  (cond ; reuse empty collection in special cases
   [(set-empty? xs) -ρ⊥]
   [else (for/fold ([ρ* : -ρ -ρ⊥]) ([x xs])
           (hash-set ρ* x (ρ@ ρ x)))]))

(: ρ+ : -ρ (U -x Symbol) -α.x → -ρ)
;; Extend environment with new mapping from symbol to address
(define (ρ+ ρ x α)
  (define s (match x [(-x s) s] [(? symbol? s) s]))
  (hash-set ρ s α))

(: ρ@ : -ρ (U -x Symbol) → -α.x)
;; Look up environment for address at given variable
(define (ρ@ ρ x)
  (define s (match x [(-x s) s] [(? symbol? s) s]))
  (hash-ref ρ s))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) (in-hash ρ)])
    `(,x ↦ ,(show-α α))))
