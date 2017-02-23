#lang typed/racket/base

(require racket/match
         racket/set
         racket/contract
         "../utils/set.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../reduction/compile/app.rkt"
         "def-ext.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (unsafe-struct-ref l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wᵥ any/c] [Wᵢ integer?])
  (match-define (-Σ σ _ M) Σ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
  (define sₐ
    (match* (Vᵥ Vᵢ)
      [((or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _))
        (-b (? index? i)))
       #:when 𝒾
       (-?@ (-st-ac 𝒾 i) sᵥ)]
      [(_ _) (-?@ 'unsafe-struct-ref sᵥ sᵢ)]))
  (match Vᵥ
    [(-St 𝒾 ⟪α⟫s)
     (define n (get-struct-arity 𝒾))
     (for/union : (℘ -ς) ([⟪α⟫ᵢ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (for/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵢ ⟪α⟫)))])
                           (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
    [(-St* (-St/C _ 𝒾 ⟪γ⟫ℓs) ⟪α⟫ᵥ l³)
     (define n (get-struct-arity 𝒾))
     (match-define (-l³ l+ l- lo) l³)
     (for/union : (℘ -ς) ([⟪γ⟫ℓ (in-list ⟪γ⟫ℓs)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (cond
                  [(struct-mutable? 𝒾 (assert i index?))
                   (define c (⟪α⟫->s (car ⟪γ⟫ℓ)))
                   (for*/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                         [C (in-set (σ@ σ (car ⟪γ⟫ℓ)))])
                     (app lo $ ℒ -unsafe-struct-ref/W (list (-W¹ V sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ
                          (mon.c∷ l³ (ℒ-with-mon ℒ (cdr (assert ⟪γ⟫ℓ))) (-W¹ C c) ⟦k⟧)))]
                  [else
                   (for*/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                         [C (in-set (σ@ σ (car ⟪γ⟫ℓ)))])
                     (app lo $ ℒ -unsafe-struct-ref/W (list (-W¹ V sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ ⟦k⟧))]))]
    [_
     (⟦k⟧ (-W -●/Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

(def-ext unsafe-struct-set! (any/c integer? . -> . void?))
