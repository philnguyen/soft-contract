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
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "def.rkt"
         "signatures.rkt")

(define-unit prims-08@
  (import meta-functions^
          prim-runtime^
          val^ sto^
          exec^
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
      ((: reduce-contracts : Σ ℓ W (ℓ V^ V^ → (Values V ΔΣ)) V^ → (Values R (℘ Err)))
       (define (reduce-contracts Σ ℓ W-fields comb V₀)
         (define-values (Vₐ ΔΣₐ)
           (match W-fields
             ['() (values V₀ ⊥ΔΣ)]
             [(cons Vₗ Wᵣ)
              (let loop : (Values V^ ΔΣ) ([Vₗ : V^ Vₗ] [Wᵣ : W Wᵣ] [i : Natural 0])
                (match Wᵣ
                  ['() (values Vₗ ⊥ΔΣ)]
                  [(cons Vₗ* Wᵣ*)
                   (define-values (Vᵣ ΔΣᵣ) (loop Vₗ* Wᵣ* (+ 1 i)))
                   (define-values (V* ΔΣ*) (comb (ℓ-with-id ℓ i) Vₗ Vᵣ))
                   (values {set V*} (⧺ ΔΣᵣ ΔΣ*))]))]))
         (just Vₐ ΔΣₐ)))
    
    (def (or/c Σ ℓ₀ W)
      #:init []
      #:rest [W (listof contract?)]
      (: step : ℓ V^ V^ → (Values V ΔΣ))
      (define (step ℓ V₁ V₂)
        (define α₁ (α:dyn (β:or/c:l ℓ) H₀))
        (define α₂ (α:dyn (β:or/c:r ℓ) H₀))
        (values (Or/C α₁ α₂ ℓ) (⧺ (alloc α₁ V₁) (alloc α₂ V₂))))
      (reduce-contracts Σ ℓ₀ W step {set 'none/c}))
    
    (def (and/c Σ ℓ₀ W)
      #:init ()
      #:rest [W (listof contract?)]
      (: step : ℓ V^ V^ → (Values V ΔΣ))
      (define (step ℓ V₁ V₂)
        (define α₁ (α:dyn (β:and/c:l ℓ) H₀))
        (define α₂ (α:dyn (β:and/c:r ℓ) H₀))
        (values (And/C α₁ α₂ ℓ) (⧺ (alloc α₁ V₁) (alloc α₂ V₂))))
      (reduce-contracts Σ ℓ₀ W step {set 'any/c})))

  (def (not/c Σ ℓ W)
    #:init ([V flat-contract?])
    (define α (α:dyn (β:not/c ℓ) H₀))
    (define ℓ* (ℓ-with-id ℓ 'not/c))
    (just (Not/C α ℓ) (alloc α V)))
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
  (def (one-of/c Σ ℓ W)
    #:init ()
    #:rest [W (listof any/c)]
    (define vals
      (map (match-lambda
             [(singleton-set (-b b)) b]
             [V^ (error 'one-of/c "only support simple values, got ~a" V^)])
           W))
    (just (One-Of/C (list->set vals)) ⊥ΔΣ))
  #;[symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
  (def (vectorof Σ ℓ W) ; FIXME uses
    #:init ([V contract?])
    (define α (α:dyn (β:vectof ℓ) H₀))
    (just (Vectof/C α ℓ) (alloc α V)))
  (def vector-immutableof (contract? . -> . contract?))
  (def (vector/c Σ ℓ W)
    #:init ()
    #:rest [W (listof contract?)]
    (define-values (αs ΔΣ) (alloc-each W (λ (i) (β:vect/c ℓ i))))
    (just (Vect/C αs ℓ) ΔΣ))
  #;[vector-immutable/c
     (() #:rest (listof contract?) . ->* . contract?)]
  (def box/c ; FIXME uses
    (contract? . -> . contract?))
  (def box-immutable/c (contract? . -> . contract?))
  (def (listof Σ ℓ W)
    #:init ([C contract?])
    (define α₀ (γ:imm 'null?))
    (define α₁ (α:dyn (β:or/c:r ℓ) H₀))
    (define αₕ (α:dyn (β:st/c -𝒾-cons ℓ 0) H₀))
    (define αₜ (α:dyn (β:st/c -𝒾-cons ℓ 1) H₀))
    (define αₗ (α:dyn (β:x/c (+x!/memo 'listof ℓ)) H₀))
    (define Disj (Or/C α₀ α₁ ℓ))
    (define Cons (St/C -𝒾-cons (list αₕ αₜ) ℓ))
    (define Cₐ {set (X/C αₗ)})
    (just Cₐ (⧺ (alloc αₗ {set Disj})
                (alloc α₁ {set Cons})
                (alloc αₕ (unpack C Σ))
                (alloc αₜ Cₐ))))
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
