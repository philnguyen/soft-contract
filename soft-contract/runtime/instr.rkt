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

    (define arg-compat? : ((U (℘ -h) -⟦e⟧) (U (℘ -h) -⟦e⟧) → Boolean)
      (match-lambda**
       [((? set? s₁) (? set? s₂))
        (or (for/and : Boolean ([h₂ (in-set s₂)])
              (equal? '✓ (ps⇒p s₁ h₂)))
            (for/and : Boolean ([h₁ (in-set s₁)])
              (equal? '✓ (ps⇒p s₂ h₁))))]
       [(a₁ a₂) #t #|TODO bad for unsafe/cpstak|# #;(equal? a₁ a₂)]))

    (define arg⊕ : ((U (℘ -h) -⟦e⟧) (U (℘ -h) -⟦e⟧) → (U (℘ -h) -⟦e⟧))
      (match-lambda**
       [((? set? s₀) (? set? s))
        (ps⊕ s₀ s)]
       [(a₀ a) a₀]))
    
    (define match? : ((U -edge -ℒ) → Boolean)
      (match x
        [(? -ℒ? ℒ) (λ (x*) (equal? ℒ x*))]
        [(-edge tgt src abs-args)
         (define num-args (length abs-args))
         (match-lambda
           [(-edge tgt* _ abs-args*)
            (and (equal? tgt tgt*)
                 (= num-args (length abs-args*))
                 (andmap arg-compat? abs-args abs-args*))]
           [_ #f])]))

    (define approx : ((U -edge -ℒ) → (U -edge -ℒ))
      (match-lambda
        [(? -ℒ? ℒ) ℒ]
        [(-edge tgt src abs-args)
         (define num-args (length abs-args))
         (define abs-args*
           (for/fold : (Listof (U (℘ -h) -⟦e⟧))
                     ([abs-args : (Listof (U (℘ -h) -⟦e⟧)) abs-args])
                     ([x₀ (in-list ℋ)])
             (match x₀
               [(-edge tgt₀ _ abs-args₀)
                #:when (and (equal? tgt tgt₀) (= num-args (length abs-args₀)))
                (map arg⊕ abs-args₀ abs-args)]
               [_ abs-args])))
         (-edge tgt src abs-args*)]))

    (define ?ℋ (memf match? ℋ))
    (with-debugging/off ((ℋ*) #;(cons (approx x) (if ?ℋ (cdr ?ℋ) ℋ))
                         (if ?ℋ ?ℋ (cons x ℋ)))
      (printf "ℋ+: ~a~n" (show-edge x))
      (printf "Old: ~a~n" (-ℋ->-⟪ℋ⟫ ℋ))
      (for ([edge (in-list ℋ)])
        (printf " - ~a~n" (show-edge edge)))
      (printf "New: ~a~n" (-ℋ->-⟪ℋ⟫ ℋ*))
      (for ([edge (in-list ℋ*)])
        (printf " - ~a~n" (show-edge edge)))
      (printf "Enter to continue:")
      (read-line)
      (printf "~n")))
  
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
