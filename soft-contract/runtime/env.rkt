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

  (: ρ@ : -ρ Symbol → ⟪α⟫)
  (define (ρ@ ρ x)
    (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
  (define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

  ;; HACK for distinguishing allocation contexts between 0-arg thunks,
  ;; which is important if the thunk returns different values (e.g. vector)
  ;; for different contexts
  (define -x-dummy (+x! 'dummy)))
