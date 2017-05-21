#lang typed/racket/base

(require typed/racket/unit
         "signatures.rkt"
         "../ast/definition.rkt")

(provide env@)

(define-unit env@
  (import)
  (export env^)

  (define ⊥ρ : -ρ (hasheq))
  (define (ρ@ [ρ : -ρ] [x : Symbol]) : ⟪α⟫
    (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
  (define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

  ;; HACK for distinguishing allocation contexts between 0-arg thunks,
  ;; which is important if the thunk returns different values (e.g. vector)
  ;; for different contexts
  (define -x-dummy (+x! 'dummy)))
