#lang typed/racket/base

(provide memoize@)

(require racket/match
         typed/racket/unit
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "../signatures.rkt")

(define-unit memoize@
  (import for-gc^ pretty-print^)
  (export memoize^)
  
  (define/memoeq (memoize-⟦e⟧ [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
    (define-type Key (List -$ -⟪ℋ⟫ -ρ -Γ))
    (define-type Rec (List (HashTable ⟪α⟫ (℘ -V)) (℘ -ς)))
    (let ([m : (HashTable Key Rec) (make-hash)])
      (remember-e! (assert (recall-e ⟦e⟧))
                   (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
                     (define key : Key (list $ ⟪ℋ⟫ ρ Γ))
                     (define σ (-Σ-σ Σ))

                     (: recompute! : → (℘ -ς))
                     (define (recompute!)
                       (define ans (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧))
                       (hash-set! m key (list σ ans))
                       ans)

                     ;; Cache result based on rest of components
                     (cond [(hash-ref m key #f) =>
                            (λ ([rec : Rec])
                              (match-define (list σ₀ ςs₀) rec)
                              (cond [(map-equal?/spanning-root σ₀ σ (ρ->⟪α⟫s ρ) V->⟪α⟫s)
                                     #;(printf "hit-e: ~a~n" (show-⟦e⟧ ⟦e⟧))
                                     ςs₀]
                                    [else (recompute!)]))]
                           [else (recompute!)])))))
  )
