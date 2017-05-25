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

  (: unpack-ℒ : -ℒ → (Values ℓ -l))
  (define (unpack-ℒ ℒ)
    (define ℓ (-ℒ-app ℒ))
    (values ℓ (ℓ-src ℓ)))

  (: ℒ-with-mon : -ℒ ℓ → -ℒ)
  (define (ℒ-with-mon ℒ ℓ)
    (match-define (-ℒ ℓs ℓₐ) ℒ)
    (-ℒ (set-add ℓs ℓ) ℓₐ))

  (: ℒ-with-l : -ℒ -l → -ℒ)
  (define (ℒ-with-l ℒ l)
    (match-define (-ℒ ℓs ℓₐ) ℒ)
    (match-define (loc _ line col id) (ℓ->loc ℓₐ))
    (-ℒ ℓs (loc->ℓ (loc l line col id))))

  (: ℋ+ : -ℋ (U -edge -ℒ)  → -ℋ)
  ;; Add edge on top of call history.
  ;; If the target is already there, return the history chunk up to first time the target
  ;; is seen
  (define (ℋ+ ℋ x)
    (define match? : ((U -edge -ℒ) → Boolean)
      (match x
        [(? -ℒ? ℒ) (λ (x*) (equal? ℒ x*))]
        [(-edge tgt src abs-args)
         (match-lambda
           [(-edge tgt* _ abs-arg*)
            (and (equal? tgt tgt*)
                 )]
           [_ #f])]))
    
    (define ?ℋ (memf match? ℋ))
    (if ?ℋ ?ℋ (cons x ℋ)))
  
  (define ⟪ℋ⟫∅
    (let ([ℋ∅ : -ℋ '()])
      (-ℋ->-⟪ℋ⟫ ℋ∅)))

  (: ⟪ℋ⟫+ : -⟪ℋ⟫ (U -edge -ℒ) → -⟪ℋ⟫)
  (define (⟪ℋ⟫+ ⟪ℋ⟫ e)
    (-ℋ->-⟪ℋ⟫ (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e)))

  (: s⊑ : (℘ -h) (℘ -h) → Boolean)
  (define (s⊑ s₁ s₂)
    (for/and : Boolean ([h₂ (in-set s₂)])
      (equal? '✓ (ps⇒p s₁ h₂)))))
