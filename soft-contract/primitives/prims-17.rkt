#lang typed/racket/base

(provide prims-17@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         racket/unsafe/ops
         set-extras
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "def-prim.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-17@
  (import prim-runtime^ proof-system^ widening^ app^ kont^ val^ pc^ sto^ instr^ env^ pretty-print^)
  (export)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; 17.1 Unsafe Numeric Operations
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-alias unsafe-fx+ +)
  (def-alias unsafe-fx- -)
  (def-alias unsafe-fx* *)
  (def-alias unsafe-fxquotient quotient)
  (def-alias unsafe-fxremainder remainder)
  (def-alias unsafe-modulo modulo)
  (def-alias unsafe-abs abs)
  (def-alias unsafe-fx= =)
  (def-alias unsafe-fx< <)
  (def-alias unsafe-fx> >)
  (def-alias unsafe-fx<= <=)
  (def-alias unsafe-fx>= >=)
  (def-alias unsafe-fxmin min)
  (def-alias unsafe-fxmax max)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Data Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-alias unsafe-car car)
  (def-alias unsafe-cdr cdr)
  (def-alias unsafe-vector-length vector-length)
  (def-alias unsafe-vector-ref vector-ref)
  (def-alias unsafe-vector-set! vector-set!)

  (def-ext (unsafe-struct-ref ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ any/c] [Wᵢ integer?])
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (define sₐ
      (match* (Vᵥ Vᵢ)
        [((or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _))
          (-b (? index? i)))
         #:when 𝒾
         (?t@ (-st-ac 𝒾 i) sᵥ)]
        [(_ _) (?t@ 'unsafe-struct-ref sᵥ sᵢ)]))
    (unless sₐ
      (printf "unsafe-struct-ref: ~a ~a -> ⊘~n" (show-t sᵥ) (show-t sᵢ)))
    (match Vᵥ
      [(-St 𝒾 ⟪α⟫s)
       (define n (count-struct-fields 𝒾))
       (for/union : (℘ -ς) ([⟪α⟫ᵢ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (for/union : (℘ -ς) ([V (in-set (σ@ Σ (cast ⟪α⟫ᵢ ⟪α⟫)))])
                             (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
      [(-St* (-St/C _ 𝒾 ⟪γ⟫ℓs) ⟪α⟫ᵥ l³)
       (define n (count-struct-fields 𝒾))
       (match-define (-l³ l+ l- lo) l³)
       (for/union : (℘ -ς) ([⟪γ⟫ℓ (in-list ⟪γ⟫ℓs)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (cond
                    [(struct-mutable? 𝒾 (assert i index?))
                     (define c #f #;(⟪α⟫->s (car ⟪γ⟫ℓ)))
                     (for*/union : (℘ -ς) ([V (in-set (σ@ Σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                           [C (in-set (σ@ Σ (-⟪α⟫ℓ-addr ⟪γ⟫ℓ)))])
                        (app ℓ (+W¹ 'unsafe-struct-ref) (list (-W¹ V sᵥ) Wᵢ) $ Γ* ⟪ℋ⟫ Σ
                             (mon.c∷ l³ (-⟪α⟫ℓ-loc (assert ⟪γ⟫ℓ)) (-W¹ C c) ⟦k⟧)))]
                    [else
                     (for*/union : (℘ -ς) ([V (in-set (σ@ Σ (cast ⟪α⟫ᵥ ⟪α⟫)))]
                                           [C (in-set (σ@ Σ (-⟪α⟫ℓ-addr ⟪γ⟫ℓ)))])
                       (app ℓ (+W¹ 'unsafe-struct-ref) (list (-W¹ V sᵥ) Wᵢ) $ Γ* ⟪ℋ⟫ Σ ⟦k⟧))]))]
      [_
       (⟦k⟧ (-W (list (+●)) sₐ) $ Γ ⟪ℋ⟫ Σ)]))

  (def-ext unsafe-struct-set! (any/c integer? . -> . void?)))

