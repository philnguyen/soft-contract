#lang typed/racket/base

(provide prims-17@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         racket/unsafe/ops
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "def.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-17@
  (import static-info^ prim-runtime^ proof-system^ widening^ app^ kont^
          val^ path^ sto^ instr^ env^ pretty-print^)
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

  (def (unsafe-struct-ref ℓ Vs H φ Σ ⟦k⟧)
    #:init ([Vᵥ^ any/c] [Vᵢ integer?])
    (for/union : (℘ -ς) ([Vᵥ (in-set Vᵥ^)])
      (match Vᵥ
        [(-St 𝒾 ⟪α⟫s)
         (define Vₐ^
           (for/fold ([Vₐ^ : -V^ ∅])
                     ([αᵢ (in-list ⟪α⟫s)]
                      [i : Natural (in-naturals)]
                      #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
             (V⊕ φ Vₐ^ (σ@ Σ (-φ-cache φ) αᵢ))))
         (⟦k⟧ (list Vₐ^) H φ Σ)]
        [(-St* (-St/C _ 𝒾 γℓs) αᵥ ctx)
         (define n (count-struct-fields 𝒾))
         (match-define (-ctx l+ l- lo _) ctx)
         (define Vᵥ*^ (σ@ Σ (-φ-cache φ) αᵥ))
         (for/union : (℘ -ς) ([γℓᵢ (in-list γℓs)]
                              [i : Natural (in-naturals)]
                              #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
            (define Cᵢ^ (σ@ Σ (-φ-cache φ) (-⟪α⟫ℓ-addr γℓᵢ)))
            (define ⟦k⟧* (if (struct-mutable? 𝒾 (assert i index?))
                             (mon.c∷ (ctx-with-ℓ ctx (-⟪α⟫ℓ-loc (assert γℓᵢ))) Cᵢ^ ⟦k⟧)
                             ⟦k⟧))
            (app₁ ℓ 'unsafe-struct-ref (list Vᵥ*^ Vᵢ) H φ Σ ⟦k⟧*))]
        [_
         (⟦k⟧ (list {set (-● ∅)}) H φ Σ)])))

  (def unsafe-struct-set! (any/c integer? . -> . void?)))

