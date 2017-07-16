#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/debug.rkt"
         "../ast/definition.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide instr@)

(define-unit instr@
  (import local-prover^ pretty-print^ widening^)
  (export instr^)

  (: ℋ+ : -ℋ -edge  → -ℋ)
  ;; Add edge on top of call history.
  ;; If the target is already there, return the history chunk up to first time the target
  ;; is seen
  (define (ℋ+ ℋ x)

    (: match? : (-edge → Boolean))
    (define match?
      (match-let ([(-edge tgt src) x])
        (match-lambda
          [(-edge tgt* _) (equal? tgt tgt*)])))

    (define ?ℋ (memf match? ℋ))
    (if ?ℋ ?ℋ (cons x ℋ)))
  
  (define ⟪ℋ⟫∅
    (let ([ℋ∅ : -ℋ '()])
      (-ℋ->-⟪ℋ⟫ ℋ∅)))

  (: ⟪ℋ⟫+ : -⟪ℋ⟫ -edge → -⟪ℋ⟫)
  (define (⟪ℋ⟫+ ⟪ℋ⟫ e)
    (-ℋ->-⟪ℋ⟫ (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e)))
  )
