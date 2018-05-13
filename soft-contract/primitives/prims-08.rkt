#lang typed/racket/base

(provide prims-08@)

(require racket/match
         racket/set
         racket/contract
         racket/splicing
         typed/racket/unit
         set-extras
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "def.rkt"
         "signatures.rkt")

(define-unit prims-08@
  (import meta-functions^
          prim-runtime^ evl^ sto^ val^
          step^
          prover^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.1 Data-structure Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def flat-named-contract
    (case->
     [any/c flat-contract? . -> . flat-contract?]
     [any/c flat-contract? (or/c not (-> contract? (-> integer? any/c))) . -> . flat-contract?]))
  (def any/c (any/c . -> . #t))
  (def none/c (any/c . -> . not))

  (splicing-local
      
      ((: reduce-contracts : ℓ Φ^ Σ W Ξ:co (Φ^ ℓ T^ T^ → V) T^ → (℘ Ξ))
       (define (reduce-contracts ℓ₀ Φ^ Σ W-fields Ξ comb! T₀)
         (define Tₐ : T^
           (match W-fields
             ['() T₀]
             [(cons Tₗ Wᵣ)
              (let loop! ([Tₗ : T^ Tₗ] [Wᵣ : W Wᵣ] [i : Natural 0])
                (match Wᵣ
                  ['() Tₗ]
                  [(cons Tₗ* Wᵣ*)
                   (define Tᵣ (loop! Tₗ* Wᵣ* (+ 1 i)))
                   {set (comb! Φ^ (ℓ-with-id ℓ₀ i) Tₗ Tᵣ)}]))]))
         {set (ret! (R (list Tₐ) Φ^) Ξ Σ)}))
    
    (def (or/c W ℓ₀ Φ^₀ Ξ Σ)
      #:init []
      #:rest [W (listof contract?)]
      (define H (Ξ:co-ctx Ξ))
      
      (: step! : Φ^ ℓ T^ T^ → V)
      (define (step! Φ^ ℓ₀ T₁ T₂)
        (define α₁ (mk-α (-α:or/c:l ℓ₀ H)))
        (define α₂ (mk-α (-α:or/c:r ℓ₀ H)))
        (define ℓ₁ (ℓ-with-id ℓ₀ 'left-disj))
        (define ℓ₂ (ℓ-with-id ℓ₀ 'right-disj))
        (⊔T! Σ Φ^ α₁ T₁)
        (⊔T! Σ Φ^ α₂ T₂)
        (Or/C (and (C^-flat? T₁) (C^-flat? T₂)) (αℓ α₁ ℓ₁) (αℓ α₂ ℓ₂)))
      (reduce-contracts ℓ₀ Φ^₀ Σ W Ξ step! {set 'none/c}))
    
    (def (and/c W ℓ₀ Φ^₀ Ξ Σ)
      #:init ()
      #:rest [W (listof contract?)]
      (define H (Ξ:co-ctx Ξ))
      
      (: step! : Φ^ ℓ T^ T^ → V)
      (define (step! Φ^ ℓ₀ T₁ T₂)
        (define α₁ (mk-α (-α:and/c:l ℓ₀ H)))
        (define α₂ (mk-α (-α:and/c:r ℓ₀ H)))
        (define ℓ₁ (ℓ-with-id ℓ₀ 'left-conj))
        (define ℓ₂ (ℓ-with-id ℓ₀ 'right-conj))
        (⊔T! Σ Φ^ α₁ T₁)
        (⊔T! Σ Φ^ α₂ T₂)
        (And/C (and (C^-flat? T₁) (C^-flat? T₂)) (αℓ α₁ ℓ₁) (αℓ α₂ ℓ₂)))
      (reduce-contracts ℓ₀ Φ^₀ Σ W Ξ step! {set 'any/c})))

  (def (not/c W ℓ Φ^ Ξ Σ)
    #:init ([V flat-contract?])
    (define α (mk-α (-α:not/c ℓ (Ξ:co-ctx Ξ))))
    (define ℓ* (ℓ-with-id ℓ 'not/c))
    {set (ret! (T->R (Not/C (αℓ α ℓ*)) Φ^) Ξ Σ)})
  (def* (=/c </c >/c <=/c >=/c) ; TODO
    (real? . -> . flat-contract?))
  (def between/c (real? real? . -> . flat-contract?))
  [def-alias real-in between/c]
  (def integer-in (exact-integer? exact-integer? . -> . flat-contract?))
  (def char-in (char? char? . -> . flat-contract?))
  (def-alias natural-number/c exact-nonnegative-integer?)
  (def string-len/c (real? . -> . flat-contract?))
  (def-alias false/c not)
  (def-pred printable/c)
  (def (one-of/c W ℓ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof any/c)]
    (define vals
      (map (match-lambda
             [(singleton-set (-b b)) b]
             [V^ (error 'one-of/c "only support simple values for not, got ~a" V^)])
           W))
    {set (ret! (T->R (One-Of/C vals) Φ^) Ξ Σ)})
  #;[symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
  (def (vectorof W ℓ Φ^ Ξ Σ) ; FIXME uses
    #:init ([T contract?])
    (define α (mk-α (-α:vectof ℓ (Ξ:co-ctx Ξ))))
    (⊔T! Σ Φ^ α T)
    {set (ret! (T->R (Vectof (αℓ α (ℓ-with-id ℓ 'vectorof))) Φ^) Ξ Σ)})
  (def vector-immutableof (contract? . -> . contract?))
  (def (vector/c W ℓ₀ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof contract?)]
    (define H (Ξ:co-ctx Ξ))
    ; FIXME uses ; FIXME check for domains to be listof contract
    (define αℓs : (Listof αℓ) ; with side-effect allocating
      (for/list ([Tᵢ (in-list W)] [i (in-naturals)] #:when (index? i))
        (define αᵢ (mk-α (-α:vect/c ℓ₀ H i)))
        (⊔T! Σ Φ^ αᵢ Tᵢ)
        (αℓ αᵢ (ℓ-with-id ℓ₀ i))))
    {set (ret! (T->R (Vect/C αℓs) Φ^) Ξ Σ)})
  #;[vector-immutable/c
     (() #:rest (listof contract?) . ->* . contract?)]
  (def box/c ; FIXME uses
    (contract? . -> . contract?))
  (def box-immutable/c (contract? . -> . contract?))
  (def (listof W ℓ Φ^ Ξ Σ)
    #:init ([C contract?])
    (define H (Ξ:co-ctx Ξ))
    (define flat? (C^-flat? C))
    (define α₀ (mk-α (-α:imm 'null?)))
    (define α₁ (mk-α (-α:or/c:r ℓ H)))
    (define αₕ (mk-α (-α:struct/c -𝒾-cons ℓ H 0)))
    (define αₜ (mk-α (-α:struct/c -𝒾-cons ℓ H 1)))
    (define αₗ (mk-α (-α:x/c (+x!/memo 'listof ℓ) H)))
    (define ℓ₀ (ℓ-with-id ℓ 'null?))
    (define ℓ₁ (ℓ-with-id ℓ 'pair?))
    (define ℓₕ (ℓ-with-id ℓ 'elem))
    (define ℓₜ (ℓ-with-id ℓ 'rest))
    (define Disj (Or/C flat? (αℓ α₀ ℓ₀) (αℓ α₁ ℓ₁)))
    (define Cons (St/C flat? -𝒾-cons (list (αℓ αₕ ℓₕ) (αℓ αₜ ℓₜ))))
    (define Ref (X/C αₗ))
    (⊔T! Σ Φ^ αₗ Disj)
    (⊔T! Σ Φ^ α₁ Cons)
    (⊔T! Σ Φ^ αₕ C)
    (⊔T! Σ Φ^ αₜ Ref)
    {set (ret! (T->R Ref Φ^) Ξ Σ)})
  (def non-empty-listof (contract? . -> . list-contract?))
  (def list*of (contract? . -> . contract?))
  (def cons/c (contract? contract? . -> . contract?))
  (def list/c (() #:rest (listof contract?) . ->* . list-contract?))
  (def syntax/c (flat-contract? . -> . flat-contract?))
  (def parameter/c ; FIXME uses
    (contract? . -> . contract?))
  (def procedure-arity-includes/c
    (exact-nonnegative-integer? . -> . flat-contract?))
  #;(def (hash/c ℓ Vs H φ Σ ⟦k⟧) ; FIXME uses
    #:init ([Vₖ contract?] [Vᵥ contract?])
    (define αₖ (mk-α (-α.hash/c-key ℓ H)))
    (define αᵥ (mk-α (-α.hash/c-val ℓ H)))
    (define φ* (alloc Σ (alloc Σ φ αₖ Vₖ) αᵥ Vᵥ))
    (define V (-Hash/C (αℓ αₖ (ℓ-with-id ℓ 'hash/c.key)) (αℓ αᵥ (ℓ-with-id ℓ 'hash/c.val))))
    (⟦k⟧ (list {set V}) H φ* Σ))
  (def channel/c (contract? . -> . contract?))
  (def continuation-mark-key/c (contract? . -> . contract?))
  ;;[evt/c (() #:rest (listof chaperone-contract?) . ->* . chaperone-contract?)]
  (def promise/c (contract? . -> . contract?))
  (def flat-contract (flat-contract? . -> . flat-contract?))
  (def flat-contract-predicate (flat-contract? . -> . (any/c . -> . any/c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.2 Function Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-opq predicate/c contract?)
  (def-opq the-unsupplied-arg unsupplied-arg?)
  (def-pred unsupplied-arg?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; TODO
  (def contract-first-order-passes? (contract? any/c . -> . boolean?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-pred contract?)
  (def-pred chaperone-contract?)
  (def-pred impersonator-contract?)
  (def-pred flat-contract?)
  (def-pred list-contract?)
  (def contract-name (contract? . -> . any/c))
  (def value-contract (has-contract? . -> . (or/c contract? not)))
  [def-pred has-contract?]
  (def value-blame (has-blame? . -> . (or/c blame? not)))
  [def-pred has-blame?]
  (def contract-projection (contract? . -> . (blame? . -> . (any/c . -> . any/c))))
  (def make-none/c (any/c . -> . contract?))
  (def-opq contract-continuation-mark-key continuation-mark-key?))
