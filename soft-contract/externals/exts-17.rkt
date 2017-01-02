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
  (define sₐ (-?@ 'unsafe-struct-ref sᵥ sᵢ))
  (match Vᵥ
    [(-St 𝒾 ⟪α⟫s)
     (define n (get-struct-arity 𝒾))
     (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (for/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ -⟪α⟫)))])
                           (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
    [(-St* 𝒾 ⟪γ⟫s ⟪α⟫ l³)
     (define n (get-struct-arity 𝒾))
     (match-define (-l³ l+ l- lo) l³)
     (for/union : (℘ -ς) ([⟪γ⟫ (in-list ⟪γ⟫s)]
                          [i : Natural (in-naturals)]
                          #:when (plausible-index? M σ Γ Wᵢ i))
                (define Γ* (Γ+ Γ (-?@ '= sᵢ (-b i))))
                (define c (and ⟪γ⟫ (⟪α⟫->s ⟪γ⟫)))
                (for*/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ -⟪α⟫)))]
                                      [C (in-set (if ⟪γ⟫ (σ@ σ (cast ⟪γ⟫ -⟪α⟫)) {set #f}))])
                            (cond
                              [C
                               (app lo $ ℒ -unsafe-struct-ref/W (list (-W¹ V sᵥ)) Γ* ⟪ℋ⟫ Σ
                                    (mon.c∷ l³ ℒ (-W¹ C c) ⟦k⟧))]
                              [else
                               (app lo $ ℒ -unsafe-struct-ref/W (list (-W¹ V sᵥ)) Γ* ⟪ℋ⟫ Σ ⟦k⟧)])))]
    [_
     (⟦k⟧ (-W -●/Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

(def-ext unsafe-struct-set! (any/c integer? . -> . void?))
