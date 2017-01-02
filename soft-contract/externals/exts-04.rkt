#lang typed/racket/base

(require racket/match
         racket/set
         racket/contract
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../reduction/compile/app.rkt"
         "def-ext.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (vector-ref l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wᵥ vector?] [Wᵢ integer?])
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
  (define sₐ (-?@ 'vector-ref sᵥ sᵢ))
  (match Vᵥ
    [(-Vector ⟪α⟫s)
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (for/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ -⟪α⟫)))])
                           (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
    [(-Vector^ α n)
     #;(begin
         (printf "vector-ref: ~a ~a~n" (show-W¹ Wᵥ) (show-W¹ Wᵢ))
         (printf "  - result: ~a~n" (set-map (σ@ σ α) show-V)))
     (for*/union : (℘ -ς) ([V (σ@ σ α)])
                 (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ))]
    [(-Vector/hetero ⟪α⟫s l³)
     (match-define (-l³ _ _ lo) l³)
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (define c (⟪α⟫->s (cast ⟪α⟫ -⟪α⟫)))
                (for/union : (℘ -ς) ([C (in-set (σ@ σ (cast ⟪α⟫ -⟪α⟫)))])
                           (mon l³ $ ℒ (-W¹ C c) (-W¹ -●/V sₐ) Γ* ⟪ℋ⟫ Σ ⟦k⟧)))]
    [(-Vector/homo ⟪α⟫ l³)
     (match-define (-l³ _ _ lo) l³)
     (define c (⟪α⟫->s ⟪α⟫))
     (for/union : (℘ -ς) ([C (σ@ σ ⟪α⟫)])
                (mon l³ $ ℒ (-W¹ C c) (-W¹ -●/V sₐ) Γ ⟪ℋ⟫ Σ ⟦k⟧))]
    [_
     (⟦k⟧ (-W -●/Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

(def-ext (vector-set! l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wᵥ vector?] [Wᵢ integer?] [Wᵤ any/c])
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
  (match-define (-W¹ Vᵤ sᵤ) Wᵤ)
  (define Wₕᵥ (-W¹ (σ@¹ σ (-α->-⟪α⟫ (-α.def havoc-𝒾))) havoc-𝒾))

  (match Vᵥ
    [(-Vector ⟪α⟫s)
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (σ⊕! σ ⟪α⟫ Vᵤ #:mutating? #t)
                (⟦k⟧ -Void/W $ Γ* ⟪ℋ⟫ Σ))]
    [(-Vector^ α n)
     (σ⊕! σ α Vᵤ #:mutating? #t)
     #;(begin
         (printf "vector-set!: ~a ~a ~a~n" (show-W¹ Wᵥ) (show-W¹ Wᵢ) (show-W¹ Wᵤ))
         (printf "  - after: ~a~n" (set-map (σ@ σ α) show-V)))
     (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
    [(-Vector/hetero ⟪α⟫s l³)
     (match-define (-l³ l+ l- lo) l³)
     (define l³* (-l³ l- l+ lo))
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (define c (⟪α⟫->s (cast ⟪α⟫ -⟪α⟫)))
                (for/union : (℘ -ς) ([C (in-set (σ@ σ (cast ⟪α⟫ -⟪α⟫)))])
                           (define W-c (-W¹ C c))
                           (define ⟦hv⟧
                             (let ([⟦chk⟧ (mk-mon-⟦e⟧ l³* ℒ (mk-rt-⟦e⟧ W-c) (mk-rt-⟦e⟧ Wᵤ))])
                               (mk-app-⟦e⟧ havoc-path ℒ (mk-rt-⟦e⟧ Wₕᵥ) (list ⟦chk⟧))))
                           ((mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ (-W¹ 'void 'void)) (list ⟦hv⟧)) ⊥ρ $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)))]
    [(-Vector/homo ⟪α⟫ l³)
     (define c (⟪α⟫->s ⟪α⟫))
     (define l³* (swap-parties l³))
     (for/union : (℘ -ς) ([C (σ@ σ ⟪α⟫)])
                (define W-c (-W¹ C c))
                (define ⟦hv⟧
                  (let ([⟦chk⟧ (mk-mon-⟦e⟧ l³* ℒ (mk-rt-⟦e⟧ W-c) (mk-rt-⟦e⟧ Wᵤ))])
                    (mk-app-⟦e⟧ havoc-path ℒ (mk-rt-⟦e⟧ Wₕᵥ) (list ⟦chk⟧))))
                ((mk-app-⟦e⟧ havoc-path ℒ (mk-rt-⟦e⟧ (-W¹ 'void 'void)) (list ⟦hv⟧)) ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
    [_
     (∪ (if (behavioral? σ (-W¹-V Wᵤ))
            (app havoc-path $ ℒ Wₕᵥ (list Wᵤ) Γ ⟪ℋ⟫ Σ ⟦k⟧)
            ∅)
        (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ))]))
