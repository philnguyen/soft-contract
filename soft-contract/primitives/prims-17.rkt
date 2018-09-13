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
  (import static-info^
          evl^ sto^ val^
          prim-runtime^ prover^
          step^ app^ approx^)
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

  (def (unsafe-struct-ref W ℓ Φ^ Ξ₀ Σ)
    #:init ([Tᵥ any/c] [Tᵢ integer?])
    (set-union-map
     (match-lambda
       [(St 𝒾 αs)
         (define Vₐ^
           (for/fold ([acc : V^ ∅])
                     ([αᵢ (in-list αs)]
                      [i : Natural (in-naturals)]
                      #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
             ((iter-⊔ V^⊔) acc (Σᵥ@ Σ αᵢ))))
         {set (ret! (T->R Vₐ^ Φ^) Ξ₀ Σ)}]
        [(X/G ctx (St/C _ 𝒾 αℓs) αᵥ)
         (define n (count-struct-fields 𝒾))
         (match-define (Ctx l+ l- lo _) ctx)
         (define Tᵥ* (Σᵥ@ Σ αᵥ))
         (for/union : (℘ Ξ) ([αℓᵢ (in-list αℓs)]
                             [i : Natural (in-naturals)]
                             #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
            (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
            (define Ξ*
              (if (struct-mutable? 𝒾 (assert i index?))
                  (K+ (F:Mon:C (Ctx-with-origin ctx ℓᵢ) (Σᵥ@ Σ αᵢ)) Ξ₀)
                  Ξ₀))
            ((app₁ 'unsafe-struct-ref) (list Tᵥ* Tᵢ) ℓ Φ^ Ξ* Σ))]
        [_ {set (ret! (T->R (-● ∅) Φ^) Ξ₀ Σ)}])
     (T->V Σ Φ^ Tᵥ)))

  (def unsafe-struct-set! (any/c integer? . -> . void?)))

