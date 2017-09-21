#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/debug.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide instr@)

(define-unit instr@
  (import local-prover^ pretty-print^ widening^)
  (export instr^)

  (: ℋ+ : -ℋ -edge  → (Values -ℋ Boolean))
  ;; Add edge on top of call history.
  ;; If the target is already there, return the history chunk up to first time the target
  ;; is seen
  (define (ℋ+ ℋ x)

    (: match? : (-edge → Boolean))
    (define match?
      (match-let ([(-edge tgt src) x])
        (match-lambda
          [(-edge tgt* _) (and (not (symbol? tgt*)) (equal? tgt tgt*))])))

    (define ?ℋ (memf match? ℋ))
    (if ?ℋ (values ?ℋ #t) (values (cons x ℋ) #f)))
  
  (define ⟪ℋ⟫∅
    (let ([ℋ∅ : -ℋ '()])
      (-ℋ->-⟪ℋ⟫ ℋ∅)))

  (: ⟪ℋ⟫+ : -⟪ℋ⟫ -edge → (Values -⟪ℋ⟫ Boolean))
  (define (⟪ℋ⟫+ ⟪ℋ⟫ e)
    (define-values (ℋ* looped?) (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e))
    (values (-ℋ->-⟪ℋ⟫ ℋ*) looped?))
  )
