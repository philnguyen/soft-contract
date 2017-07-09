#lang typed/racket/base

(provide memoize@)

(require racket/match
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "../signatures.rkt")

(define-unit memoize@
  (import for-gc^ pretty-print^)
  (export memoize^)

  (define/memoeq (memoize-⟦k⟧ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (define-type Key (List -A -Γ -⟪ℋ⟫))
    (define-type Rec (List -σ (℘ -ς)))
    (let ([m : (HashTable Key Rec) (make-hash)])
      (define ⟦k⟧* : -⟦k⟧
        (λ (A $ Γ ⟪ℋ⟫ Σ)
          (match-define (-Σ σ _) Σ)
          (define key (list A Γ ⟪ℋ⟫))
          
          (: recompute! : → (℘ -ς))
          (define (recompute!)
            (define ans (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))
            (hash-set! m key (list σ ans))
            ans)

          ;; Cache result based on rest of components
          (cond [(hash-ref m key #f) =>
                 (λ ([rec : Rec])
                   (match-define (list σ₀ ςs₀) rec)
                   (define root : (℘ ⟪α⟫)
                     (∪ (⟦k⟧->roots ⟦k⟧)
                        (match A
                          [(-W Vs _) (->⟪α⟫s Vs)]
                          [_ ∅eq])))
                   (cond [(σ-equal?/spanning-root σ₀ σ root)
                          #;(begin
                              (printf "hit-k over ~a~n" (set-map root show-⟪α⟫))
                              (printf "  - old: ~a~n" (show-σ σ₀))
                              (printf "  - new: ~a~n" (show-σ σ )))
                          ςs₀]
                         [else (recompute!)]))]
                [else (recompute!)])))
      (add-⟦k⟧-roots! ⟦k⟧* (⟦k⟧->roots ⟦k⟧))
      (set-⟦k⟧->αₖ! ⟦k⟧* (⟦k⟧->αₖ ⟦k⟧))
      ⟦k⟧*))

  (define/memoeq (memoize-⟦e⟧ [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
    (define-type Key (List -⟪ℋ⟫ -ρ -Γ))
    (define-type Rec (List (HashTable ⟪α⟫ (℘ -V)) (℘ -ς)))
    (let ([m : (HashTable Key Rec) (make-hash)])
      (remember-e! (assert (recall-e ⟦e⟧))
                   (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
                     (match-define (-Σ (-σ mσ _ _) _) Σ)
                     (define key : Key (list ⟪ℋ⟫ ρ Γ))

                     (: recompute! : → (℘ -ς))
                     (define (recompute!)
                       (define ans (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧))
                       (hash-set! m key (list mσ ans))
                       ans)

                     ;; Cache result based on rest of components
                     (cond [(hash-ref m key #f) =>
                            (λ ([rec : Rec])
                              (match-define (list mσ₀ ςs₀) rec)
                              (cond [(map-equal?/spanning-root mσ₀ mσ (ρ->⟪α⟫s ρ) V->⟪α⟫s)
                                     #;(printf "hit-e: ~a~n" (show-⟦e⟧ ⟦e⟧))
                                     ςs₀]
                                    [else (recompute!)]))]
                           [else (recompute!)])))))
  )
