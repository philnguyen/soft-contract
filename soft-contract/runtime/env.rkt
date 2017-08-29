#lang typed/racket/base

(require typed/racket/unit
         racket/match
         "signatures.rkt"
         "../ast/signatures.rkt")

(provide env@)

(define-unit env@
  (import)
  (export env^)

  (define ⊥ρ : -ρ (hasheq))
  (define (ρ@ [ρ : -ρ] [x : Symbol]) : (U ⟪α⟫ -Seal/C)
    (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
  (define ρ+ : (-ρ Symbol (U ⟪α⟫ -Seal/C) → -ρ) hash-set)

  ;; HACK for distinguishing allocation contexts between 0-arg thunks,
  ;; which is important if the thunk returns different values (e.g. vector)
  ;; for different contexts
  (define -x-dummy (+x! 'dummy)))
