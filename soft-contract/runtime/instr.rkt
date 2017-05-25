#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/debug.rkt"
         "../ast/definition.rkt"
         "../proof-relation/signatures.rkt"
         "signatures.rkt"
         )

(provide instr@)

(define-unit instr@
  (import local-prover^ pretty-print^)
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
    (define (show-arg [arg : (U (℘ -h) -⟦e⟧)]) : Sexp
      (if (set? arg) (set-map arg show-h) (show-⟦e⟧ arg)))
    
    (define match? : ((U -edge -ℒ) → Boolean)
      (match x
        [(? -ℒ? ℒ) (λ (e) (equal? e ℒ))]
        [(-edge target call-site abstract-args)
         (match-lambda
           [(-edge target* call-site* abstract-args*)
            (and (equal? target target*)
                 (for/and : Boolean ([arg (in-list abstract-args)]
                                     [arg* (in-list  abstract-args*)])
                   (with-debugging ((res) (match* (arg arg*)
                                            [((? set? s₁) (? set? s₂))
                                             (or (s⊑ s₁ s₂) (s⊑ s₂ s₁))]
                                            [(_ _)
                                             (equal? arg arg*)]))
                     (unless res
                       (printf "~a × ~a: ~a~n" (show-arg arg) (show-arg arg*) res)))))]
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
