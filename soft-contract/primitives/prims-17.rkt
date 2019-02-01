#lang typed/racket/base

(provide prims-17@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         racket/unsafe/ops
         set-extras
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "def.rkt"
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-17@
  (import static-info^
          sto^ val^ cache^
          prim-runtime^
          prover^
          exec^ app^ mon^)
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

  (def (unsafe-struct-ref Σ ℓ W)
    #:init ([Vᵥ any/c] [Vᵢ integer?])
    ((inst fold-ans V)
     (match-lambda
       [(St 𝒾 αs)
         (define Vₐ
           (for/union : V^ ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
             (unpack αᵢ Σ)))
         (just Vₐ)]
        [(Guarded ctx (St/C 𝒾 αs _) αᵥ)
         (define Vᵥ* (unpack αᵥ Σ))
         (with-collapsing/R [(ΔΣ₀ Ws) (app Σ ℓ {set 'unsafe-struct-ref} (list Vᵥ* Vᵢ))]
           (define Σ₀ (⧺ Σ ΔΣ₀))
           (define Vₐ (car (collapse-W^ Ws)))
           (for/fold ([r : R ⊥R] [es : (℘ Err) ∅])
                     ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
             (define-values (rᵢ esᵢ) (mon Σ₀ ctx (unpack αᵢ Σ₀) Vₐ))
             (values (m⊔ r (ΔΣ⧺R ΔΣ₀ rᵢ)) (∪ es esᵢ))))]
        [_ (just (-● ∅))])
     Vᵥ))

  (def unsafe-struct-set! (any/c integer? . -> . void?)))

