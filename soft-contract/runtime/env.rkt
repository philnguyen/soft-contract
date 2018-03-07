#lang typed/racket/base

(require typed/racket/unit
         racket/match
         "signatures.rkt"
         "../ast/signatures.rkt")

(provide env@)

(define-unit env@
  (import)
  (export env^)

  (define ⊥Ρ : Ρ (hasheq))

  (: Ρ@ : Ρ Symbol → α)
  (define (Ρ@ Ρ x)
    (hash-ref Ρ x (λ () (error 'Ρ@ "~a not in env. ~a" x (hash-keys Ρ)))))

  (: Ρ@* : Ρ (Listof Symbol) → (Listof α))
  (define (Ρ@* Ρ xs) (for/list ([x (in-list xs)]) (Ρ@ Ρ x)))
  
  (define Ρ+ : (Ρ Symbol α → Ρ) hash-set)

  ;; HACK for distinguishing allocation contexts between 0-arg thunks,
  ;; which is important if the thunk returns different values (e.g. vector)
  ;; for different contexts
  (define -x-dummy (+x! 'dummy)))
