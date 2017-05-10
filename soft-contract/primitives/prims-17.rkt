#lang typed/racket/base

(provide prims-17@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         racket/unsafe/ops
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "def-prim.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-17@
  (import prim-runtime^ proof-system^ widening^ app^ kont^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Data Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-alias unsafe-car car)
  (def-alias unsafe-cdr cdr)
  (def-alias unsafe-vector-length vector-length)
  (def-alias unsafe-vector-ref vector-ref)
  (def-alias unsafe-vector-set! vector-set!)

  (def-ext (unsafe-struct-ref $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ any/c] [Wᵢ integer?])
    (match-define (-Σ σ _ M) Σ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (define sₐ
      (match* (Vᵥ Vᵢ)
        [((or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _))
          (-b (? index? i)))
         #:when 𝒾
         (?t@ (-st-ac 𝒾 i) sᵥ)]
        [(_ _) (?t@ 'unsafe-struct-ref sᵥ sᵢ)]))
    (match Vᵥ
      [(-St 𝒾 ⟪α⟫s)
       (define n (get-struct-arity 𝒾))
       (for/union : (℘ -ς) ([⟪α⟫ᵢ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? M σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (for/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵢ ⟪α⟫)))])
                             (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
      [(-St* (-St/C _ 𝒾 ⟪γ⟫ℓs) ⟪α⟫ᵥ l³)
       (define n (get-struct-arity 𝒾))
       (match-define (-l³ l+ l- lo) l³)
       (for/union : (℘ -ς) ([⟪γ⟫ℓ (in-list ⟪γ⟫ℓs)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? M σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (cond
                    [(struct-mutable? 𝒾 (assert i index?))
                     (define c #f #;(⟪α⟫->s (car ⟪γ⟫ℓ)))
                     (for*/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                           [C (in-set (σ@ σ (-⟪α⟫ℓ-addr ⟪γ⟫ℓ)))])
                                 (app $ ℒ -unsafe-struct-ref.W¹ (list (-W¹ V sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ
                                      (mon.c∷ l³ (ℒ-with-mon ℒ (-⟪α⟫ℓ-loc (assert ⟪γ⟫ℓ))) (-W¹ C c) ⟦k⟧)))]
                    [else
                     (for*/union : (℘ -ς) ([V (in-set (σ@ σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                           [C (in-set (σ@ σ (-⟪α⟫ℓ-addr ⟪γ⟫ℓ)))])
                                 (app $ ℒ -unsafe-struct-ref.W¹ (list (-W¹ V sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ ⟦k⟧))]))]
      [_
       (⟦k⟧ (-W -●.Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

  (def-ext unsafe-struct-set! (any/c integer? . -> . void?)))

