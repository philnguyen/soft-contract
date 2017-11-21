#lang typed/racket/base

(provide for-gc@)

(require typed/racket/unit
         racket/splicing
         racket/match
         racket/set
         set-extras
         "../signatures.rkt"
         "../ast/signatures.rkt"
         "../utils/main.rkt"
         "signatures.rkt"
         )

(define-unit for-gc@
  (import sto^ pretty-print^ static-info^)
  (export for-gc^)

  ;; TMP hack for part of root set from stack frames
  (splicing-let ([m ((inst make-hasheq -⟦k⟧ (℘ ⟪α⟫)))])

    (: add-⟦k⟧-roots! : -⟦k⟧ (℘ ⟪α⟫) → Void)
    (define (add-⟦k⟧-roots! ⟦k⟧ αs)
      (hash-update! m ⟦k⟧ (λ ([αs₀ : (℘ ⟪α⟫)]) (∪ αs₀ αs)) mk-∅eq))

    (: ⟦k⟧->roots : -⟦k⟧ → (℘ ⟪α⟫))
    ;; Return the root set spanned by the stack chunk for current block
    (define (⟦k⟧->roots ⟦k⟧)
      (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αs "nothing for ~a" ⟦k⟧)))))

  ;; TMP hack for mapping stack to stack address to return to
  (splicing-let ([m ((inst make-hasheq -⟦k⟧ -αₖ))])

    (: set-⟦k⟧->αₖ! : -⟦k⟧ -αₖ → Void)
    (define (set-⟦k⟧->αₖ! ⟦k⟧ αₖ)
      (hash-update! m ⟦k⟧
                    (λ ([αₖ₀ : -αₖ]) ; just for debugging
                      (assert (equal? αₖ₀ αₖ))
                      αₖ₀)
                    (λ () αₖ)))

    (: ⟦k⟧->αₖ : -⟦k⟧ → -αₖ)
    (define (⟦k⟧->αₖ ⟦k⟧)
      (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αₖ "nothing for ~a" ⟦k⟧)))))

  (define/memoeq (V->⟪α⟫s [V : -V]) : (℘ ⟪α⟫)
    (with-debugging/off
      ((αs)
       (match V
         [(-St _ αs) (list->seteq αs)]
         [(-Vector αs) (list->seteq αs)]
         [(-Vector^ α _) {seteq α}]
         [(-Ar V α _) (set-add (V->⟪α⟫s V) α)]
         [(-St* grd α _) (set-add (V->⟪α⟫s grd) α)]
         [(-Hash^ αₖ αᵥ _) {seteq αₖ αᵥ}]
         [(-Set^ α _) {seteq α}]
         [(or (-Vector/guard grd α _)
              (-Hash/guard grd α _)
              (-Set/guard grd α _))
          #:when (and grd α)
          (set-add (V->⟪α⟫s grd) α)]
         [(-Clo _ _ ρ) (ρ->⟪α⟫s ρ)]
         [(-Case-Clo cases) (for/unioneq : (℘ ⟪α⟫) ([clo cases]) (V->⟪α⟫s clo))]
         [(-And/C _ α β) {seteq (-⟪α⟫ℓ-addr α) (-⟪α⟫ℓ-addr β)}]
         [(-Or/C  _ α β) {seteq (-⟪α⟫ℓ-addr α) (-⟪α⟫ℓ-addr β)}]
         [(-Not/C α) {seteq (-⟪α⟫ℓ-addr α)}]
         [(-One-Of/C _) ∅eq]
         [(-Hash/C α β) {seteq (-⟪α⟫ℓ-addr α) (-⟪α⟫ℓ-addr β)}]
         [(-Set/C α) {seteq (-⟪α⟫ℓ-addr α)}]
         [(-x/C α) {seteq α}]
         [(-St/C _ _ αs) {list->seteq (map -⟪α⟫ℓ-addr αs)}]
         [(-Vectorof α) {seteq (-⟪α⟫ℓ-addr α)}]
         [(-Vector/C αs) (list->seteq (map -⟪α⟫ℓ-addr αs))]
         [(-=> αs βs)
          (match αs
            [(? list? αs) (set-add* (list->seteq (map -⟪α⟫ℓ-addr αs))
                                    (if (pair? βs) (map -⟪α⟫ℓ-addr βs) '()))]
            [(-var αs αᵣ)
             (set-add* (set-add (list->seteq (map -⟪α⟫ℓ-addr αs)) (-⟪α⟫ℓ-addr αᵣ))
                       (if (pair? βs) (map -⟪α⟫ℓ-addr βs) '()))])]
         [(-=>i αs (list D _ _)) (∪ (list->seteq (map -⟪α⟫ℓ-addr αs)) (V->⟪α⟫s D))]
         [(-Case-> cases)
          (for/unioneq : (℘ ⟪α⟫) ([C cases]) (V->⟪α⟫s C))]
         [(-∀/C _ _ ρ) (ρ->⟪α⟫s ρ)]
         [(-Seal/C x H _) {seteq {-α->⟪α⟫ (-α.sealed x H)}}]
         [_ ∅eq]))
      (printf "V->⟪α⟫s ~a: (~a)~n" (show-V V) (set-count αs))
      (for ([α αs])
        (printf " - ~a~n" α))
      (printf "~n")))

  (: ρ->⟪α⟫s : -ρ → (℘ ⟪α⟫))
  (define (ρ->⟪α⟫s ρ) (list->seteq (hash-values ρ)))

  (: αₖ->⟪α⟫s : -αₖ -σₖ → (℘ ⟪α⟫))
  (define (αₖ->⟪α⟫s αₖ σₖ)
    (define-set seen : -αₖ #:as-mutable-hash? #t)
    (let go ([acc : (℘ ⟪α⟫) ∅eq] [αₖ : -αₖ αₖ])
      (cond
        [(seen-has? αₖ) acc]
        [else
         (seen-add! αₖ)
         (for/fold ([acc : (℘ ⟪α⟫) (if (-HV? αₖ) (set-add acc (-α->⟪α⟫ (-α.hv (-HV-tag αₖ)))) acc)])
                   ([⟦k⟧ (in-set (hash-ref σₖ αₖ mk-∅))])
           (go (∪ acc (⟦k⟧->roots ⟦k⟧)) (⟦k⟧->αₖ ⟦k⟧)))])))

  (: ⟦k⟧->⟪α⟫s : -⟦k⟧ -σₖ → (℘ ⟪α⟫))
  (define (⟦k⟧->⟪α⟫s ⟦k⟧ σₖ)
    (∪ (⟦k⟧->roots ⟦k⟧) (αₖ->⟪α⟫s (⟦k⟧->αₖ ⟦k⟧) σₖ)))

  (: ->⟪α⟫s : (Rec X (U ⟪α⟫ -V -ρ (-var X) (Listof X) (℘ X))) → (℘ ⟪α⟫))
  (define (->⟪α⟫s x)
    (cond
      [(-var? x)
       (∪ (->⟪α⟫s (-var-rest x))
          (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-list (-var-init x))]) (->⟪α⟫s xᵢ)))]
      [(list? x)
       (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-list x)]) (->⟪α⟫s xᵢ))]
      [(set? x)
       (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-set x)]) (->⟪α⟫s xᵢ))]
      [(-V? x) (V->⟪α⟫s x)]
      [(hash? x) (ρ->⟪α⟫s x)]
      [else {seteq x}]))

  (: σ-equal?/spanning-root : -σ -σ (℘ ⟪α⟫) → Boolean)
  (define (σ-equal?/spanning-root σ₁ σ₂ root)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    
    (let go ([addrs : (℘ ⟪α⟫) root])
      (for/and : Boolean ([α : ⟪α⟫ (in-set addrs)])
        (cond
          [(seen-has? α) #t]
          [else
           (seen-add! α)
           (define Vs₁ (hash-ref σ₁ α mk-∅))
           (define Vs₂ (hash-ref σ₂ α mk-∅))
           (and (equal? Vs₁ Vs₂)
                (for/and : Boolean ([V (in-set Vs₁)])
                  (go (V->⟪α⟫s V))))]))))
  
  )
