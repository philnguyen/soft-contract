#lang typed/racket/base

(require racket/match
         racket/set
         racket/contract
         "../utils/set.rkt"
         "../utils/function.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../reduction/compile/utils.rkt"
         "../reduction/compile/app.rkt"
         "../reduction/havoc.rkt"
         "def-ext.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.9 Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (map l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  ; FIXME uses 
  #:domain ([Wₚ (any/c . -> . any/c)]
            [Wₗ list?])
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ Vₚ sₚ) Wₚ)
  (match-define (-W¹ Vₗ sₗ) Wₗ)
  (define sₐ (-?@ 'map sₚ sₗ))
  (match Vₗ
    [(-b '()) (⟦k⟧ (-W (list -null) sₐ) $ Γ ⟪ℋ⟫ Σ)]
    [(-Cons _ _)
     (define ⟦k⟧* (mk-listof∷ l sₐ ℒ ⟪ℋ⟫ ⟦k⟧))
     (for/union : (℘ -ς) ([V (extract-list-content σ Vₗ)])
       (app l $ ℒ Wₚ (list (-W¹ V #f)) Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
    [_ (⟦k⟧ (-W (list (-● (set 'list?))) sₐ) $ Γ ⟪ℋ⟫ Σ)]))

(def-ext (for-each l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wₚ (any/c . -> . any/c)]
            [Wₗ list?])
  #:result -Void/Vs)

(define/memo (mk-listof∷ [l : -l] [sₐ : -s] [ℒ₀ : -ℒ] [⟪ℋ⟫₀ : -⟪ℋ⟫] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define ⟪α⟫ₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ₀ ⟪ℋ⟫₀ 0)))
       (define ⟪α⟫ₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ₀ ⟪ℋ⟫₀ 1)))
       (define Vₚ (-Cons ⟪α⟫ₕ ⟪α⟫ₜ))
       (σ⊕*! Σ [⟪α⟫ₕ ↦ V] [⟪α⟫ₜ ↦ -null] [⟪α⟫ₜ ↦ Vₚ])
       (⟦k⟧ (-W (list Vₚ) sₐ) $ Γ ⟪ℋ⟫ Σ)]
      [_
       (define blm (blm-arity l 'mk-listof 1 Vs))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))


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
     (for/union : (℘ -ς) ([⟪α⟫ : -⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
       (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
       (for/union : (℘ -ς) ([V (in-set (σ@ σ ⟪α⟫))])
         (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
    [(-Vector^ α n)
     (for/union : (℘ -ς) ([V (σ@ σ α)])
        (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ))]
    [(-Vector/guard grd ⟪α⟫ᵥ l³)
     (match-define (-l³ _ _ lo) l³)
     (match grd
       [(-Vector/C ⟪α⟫ℓs)
        (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                             [i : Natural (in-naturals)]
                             #:when (plausible-index? M σ Γ Wᵢ i))
          (match-define (cons ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
          (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
          (define cᵢ (⟪α⟫->s ⟪α⟫ᵢ))
          (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
            (.vector-ref lo $ ℒ (list (-W¹ Vᵥ* sᵥ)) Γ* ⟪ℋ⟫ Σ
                         (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵢ) (-W¹ Cᵢ cᵢ) ⟦k⟧))))]
       [(-Vectorof ⟪α⟫ℓ)
        (match-define (cons ⟪α⟫* ℓ*) ⟪α⟫ℓ)
        (define c* (⟪α⟫->s ⟪α⟫*))
        (for/union : (℘ -ς) ([C* (in-set (σ@ σ ⟪α⟫*))]
                             [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
          (.vector-ref lo $ ℒ (list (-W¹ Vᵥ* sᵥ)) Γ ⟪ℋ⟫ Σ
                       (mon.c∷ l³ (ℒ-with-mon ℒ ℓ*) (-W¹ C* c*) ⟦k⟧)))])]
    [_
     (⟦k⟧ (-W -●/Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

(def-ext (vector-set! l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wᵥ vector?] [Wᵢ integer?] [Wᵤ any/c])
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
  (match-define (-W¹ Vᵤ sᵤ) Wᵤ)

  (match Vᵥ
    [(-Vector ⟪α⟫s)
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
       (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
       (σ⊕! Σ ⟪α⟫ Vᵤ #:mutating? #t)
       (⟦k⟧ -Void/W $ Γ* ⟪ℋ⟫ Σ))]
    [(-Vector^ α n)
     (σ⊕! Σ α Vᵤ #:mutating? #t)
     (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
    [(-Vector/guard grd ⟪α⟫ᵥ l³)
     (match-define (-l³ l+ l- lo) l³)
     (define l³* (-l³ l- l+ lo))
     (match grd
       [(-Vector/C ⟪α⟫ℓs)
        (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                             [i : Natural (in-naturals)]
                             #:when (plausible-index? M σ Γ Wᵢ i))
          (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
          (match-define (cons ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
          (define cᵢ (⟪α⟫->s ⟪α⟫ᵢ))
          (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
            (define W-c (-W¹ Cᵢ cᵢ))
            (define Wᵥ* (-W¹ Vᵥ* sᵥ))
            (define ⟦chk⟧ (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ W-c) (mk-rt-⟦e⟧ Wᵤ)))
            (⟦chk⟧ ⊥ρ $ Γ* ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* -vector-set!/W) '() ⊥ρ lo ℒ ⟦k⟧))))]
       [(-Vectorof ⟪α⟫ℓ)
        (match-define (cons ⟪α⟫* ℓ*) ⟪α⟫ℓ)
        (define c* (⟪α⟫->s ⟪α⟫*))
        (for*/union : (℘ -ς) ([C*  (in-set (σ@ σ ⟪α⟫*))]
                              [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
          (define W-c (-W¹ C* c*))
          (define Wᵥ* (-W¹ Vᵥ* sᵥ))
          (define ⟦chk⟧ (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓ*) (mk-rt-⟦e⟧ W-c) (mk-rt-⟦e⟧ Wᵤ)))
          (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* -vector-set!/W) '() ⊥ρ lo ℒ ⟦k⟧)))])]
    [_
     (if (behavioral? σ (-W¹-V Wᵤ))
         (havoc ℒ Vᵤ Γ ⟪ℋ⟫ Σ ⟦k⟧)
         (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ))]))
