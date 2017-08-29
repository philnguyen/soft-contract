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
  (define (ρ@ [ρ : -ρ] [x : Symbol]) : ⟪α⟫
    (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
  (define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

  ;; HACK for distinguishing allocation contexts between 0-arg thunks,
  ;; which is important if the thunk returns different values (e.g. vector)
  ;; for different contexts
  (define -x-dummy (+x! 'dummy))

  (: flip-seals : -ρ → -ρ)
  (define (flip-seals ρ)
    (for*/fold ([ρ : -ρ ρ])
               ([(x ⟪α⟫) (in-hash ρ)]
                [α (in-value (⟪α⟫->-α ⟪α⟫))]
                #:when (or (-α.seal? α) (-α.unseal? α)))
      (define α*
        (match α
          [(-α.seal   x ⟪ℋ⟫) (-α.unseal x ⟪ℋ⟫)]
          [(-α.unseal x ⟪ℋ⟫) (-α.seal   x ⟪ℋ⟫)]))
      (hash-set ρ x (-α->⟪α⟫ α*)))))
