#lang typed/racket/base

(provide prims-17@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         racket/unsafe/ops
         set-extras
         "../utils/patterns.rkt"
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
    ((inst fold-ans/collapsing V)
     Σ
     (match-lambda
       [(St (and α (α:dyn (β:st-elems _ 𝒾) _)) Ps)
        (define Vₐ
          (for/union : V^ ([(Xᵢ i) (in-indexed (Σ@/blob α Σ))] #:when (maybe=? Σ i Vᵢ))
            Xᵢ))
        (R-of (refine-V^ Vₐ Ps Σ))]
       [(Guarded (cons l+ l-) (? St/C? C) αᵥ)
        (define-values (αₕ ℓₕ 𝒾) (St/C-fields C))
        (define S (Σ@/blob αₕ Σ))
        (define Vᵥ* (Σ@ αᵥ Σ))
        (with-collapsing/R Σ [(ΔΣ₀ Ws) (app Σ ℓₕ {set 'unsafe-struct-ref} (list Vᵥ* Vᵢ))]
          (define Σ₀ (⧺ Σ ΔΣ₀))
          (define Vₐ (car (collapse-W^ Σ₀ Ws)))
          (define ctx (Ctx l+ l- ℓₕ ℓ))
          (for/fold ([r : R ⊥R]) ([(Cᵢ i) (in-indexed S)] #:when (maybe=? Σ i Vᵢ))
            (define rᵢ (mon Σ₀ ctx Cᵢ Vₐ))
            (R⊔ r (ΔΣ⧺R ΔΣ₀ rᵢ))))]
       [(-● Ps)
        (match Vᵢ
          [(-b (? index? i))
           (R-of (or (for/or : (Option V^) ([P (in-set Ps)] #:when (-st-p? P))
                       (match-define (-st-p 𝒾) P)
                       (st-ac-● 𝒾 i Ps Σ))
                     {set (-● ∅)}))]
          [_ (R-of {set (-● ∅)})])]
       [_ ⊥R])
     (unpack Vᵥ Σ)))

  (def unsafe-struct-set! (any/c integer? . -> . void?)))

