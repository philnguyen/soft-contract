#lang typed/racket/base

(provide fc@)

(require racket/sequence
         racket/match
         (except-in racket/set for/set for/seteq for*/set for*/seteq)
         syntax/parse/define
         typed/racket/unit
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit fc@
  (import )
  (export fc^)

  (: fc : V^ V^ ℓ Φ^ Ξ:co Σ → (℘ Ξ))
  (define (fc C V ℓ Φ^ Ξ Σ) ???)

  #|
  (: flat-chk : -l ℓ -V^ -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (flat-chk l ℓₐ C^ V^ H φ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (for/union : (℘ -ς) ([C (in-set C^)])
      (match C
        [(-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
         (define C₁ (σ@ Σ (-φ-cache φ) α₁))
         (define C₂ (σ@ Σ (-φ-cache φ) α₂))
         (push-fc l ℓ₁ C₁ V^ H φ Σ (fc-and/c∷ l ℓ₂ C₁ C₂ ⟦k⟧))]
        [(-Or/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
         (define C₁ (σ@ Σ (-φ-cache φ) α₁))
         (define C₂ (σ@ Σ (-φ-cache φ) α₂))
         (push-fc l ℓ₁ C₁ V^ H φ Σ (fc-or/c∷ l ℓ₂ C₁ C₂ V^ ⟦k⟧))]
        [(-Not/C (-⟪α⟫ℓ α ℓ*))
         (define C* (σ@ Σ (-φ-cache φ) α))
         (push-fc l ℓ* C* V^ H φ Σ (fc-not/c∷ V^ ⟦k⟧))]
        [(-One-Of/C bs)
         (case (sat-one-of V^ bs)
           [(✓) (⟦k⟧ (list {set -tt} V^) H φ Σ)]
           [(✗) (⟦k⟧ (list {set -ff}   ) H φ Σ)]
           [(?) (∪ (⟦k⟧ (list {set -tt} (list->set (set-map bs -b))) H φ Σ)
                   (⟦k⟧ (list {set -ff}) H φ Σ))])]
        [(-St/C _ s αℓs)

         (: chk-fields : -φ → (℘ -ς))
         (define (chk-fields φ)
           (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
           (define Cs (σ@/list Σ (-φ-cache φ) αs))
           (define ⟦chk-field⟧s : (Listof -⟦e⟧)
             (let ([V^* (V+ σ φ V^ (-st-p s))])
               (for/list ([Cᵢ (in-list Cs)]
                          [ℓᵢ : ℓ (in-list ℓs)]
                          [i (in-naturals)] #:when (index? i))
                 (define ⟦ref⟧ᵢ (mk-app ℓₐ (mk-V (-st-ac s i)) (list (mk-A (list V^*)))))
                 (mk-fc l ℓᵢ (mk-A (list Cᵢ)) ⟦ref⟧ᵢ))))
           (match ⟦chk-field⟧s
             ['()
              (define ⟦rt⟧ (mk-A (list {set -tt} (V+ σ φ V^ (-st-p s)))))
              (⟦rt⟧ ⊥ρ H φ Σ ⟦k⟧)]
             [(cons ⟦chk-field⟧ ⟦chk-field⟧s*)
              (⟦chk-field⟧ ⊥ρ H φ Σ (fc-struct/c∷ l ℓₐ s '() ⟦chk-field⟧s* ⊥ρ ⟦k⟧))]))

         (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ (-st-p s) V^)]) : -ς
           #:true (chk-fields φ₁)
           #:false ((mk-V -ff) ⊥ρ H φ₂ Σ ⟦k⟧))]
        [(-x/C α)
         (define C*^ (σ@ Σ (-φ-cache φ) α))
         (push-fc l ℓₐ C*^ V^ H φ Σ ⟦k⟧ #:looped #t)]
        [(? -b? b)
         (define ⟦ap⟧ (mk-app ℓₐ (mk-V 'equal?) (list (mk-A (list V^)) (mk-V b))))
         (define ⟦rt⟧ (mk-A (list {set -tt} {set b})))
         (⟦ap⟧ ⊥ρ H φ Σ (if∷ l ⟦rt⟧ (mk-V -ff) ⊥ρ ⟦k⟧))]
        [_
         (define ⟦ap⟧ (mk-app ℓₐ (mk-A (list C^)) (list (mk-A (list V^)))))
         (define ⟦rt⟧ (mk-A (list {set -tt} (V+ σ φ V^ C))))
         (⟦ap⟧ ⊥ρ H φ Σ (if∷ l ⟦rt⟧ (mk-V -ff) ⊥ρ ⟦k⟧))])))

  (: push-fc ((-l ℓ -V^ -V^ -H -φ -Σ -⟦k⟧) (#:looped Boolean) . ->* . (℘ -ς)))
  (define (push-fc l ℓ C^ V^ H φ Σ ⟦k⟧ #:looped [looped? #f])
    (if looped?
        (let ([αₖ (-αₖ H (-F l ℓ C^ V^) φ)])
          {set (-ς↑ (σₖ+! Σ αₖ ⟦k⟧))})
        (flat-chk l ℓ C^ V^ H φ Σ ⟦k⟧)))
  |#
  )
