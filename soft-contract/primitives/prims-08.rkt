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
  (import prim-runtime^ evl^ sto^ val^
          step^)
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

  #;(splicing-local
      
      ((: reduce-contracts : -l ℓ -H -φ -Σ (Listof -V^) -⟦k⟧ (-φ ℓ -V^ -V^ → (Values -V^ -φ)) (Listof -V^) → (℘ -ς))
       (define (reduce-contracts lo ℓ H φ Σ Vs ⟦k⟧ comb id)
         (match Vs
           ['() (⟦k⟧ id H φ Σ)]
           [_
            (define-values (V* φ*)
              (let loop : (Values -V^ -φ) ([φ : -φ φ] [Vs : (Listof -V^) Vs] [i : Natural 0])
                (match Vs
                  [(list V) (values V φ)]
                  [(cons Vₗ Vsᵣ)
                   (define-values (Vᵣ φᵣ) (loop φ Vsᵣ (+ 1 i)))
                   (comb φᵣ (ℓ-with-id ℓ i) Vₗ Vᵣ)])))
            (⟦k⟧ (list V*) H φ* Σ)])))
    
    (def (or/c ℓ₀ Vs H φ Σ ⟦k⟧)
      #:init []
      #:rest [Vs (listof contract?)]
      (: or/c.2 : -φ ℓ -V^ -V^ → (Values -V^ -φ))
      (define (or/c.2 φ ℓ V₁ V₂)
        (define α₁ (mk-α (-α.or/c-l ℓ H)))
        (define α₂ (mk-α (-α.or/c-r ℓ H)))
        (define ℓ₁ (ℓ-with-id ℓ 'left-disj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-disj))
        (define C (-Or/C (and (C^-flat? V₁) (C^-flat? V₂)) (αℓ α₁ ℓ₁) (αℓ α₂ ℓ₂)))
        (values {set C} (alloc Σ (alloc Σ φ α₁ V₁) α₂ V₂)))
      (reduce-contracts 'or/c ℓ₀ H φ Σ Vs ⟦k⟧ or/c.2 (list {set 'none/c})))
    
    (def (and/c ℓ₀ Vs H φ Σ ⟦k⟧)
      #:init ()
      #:rest [Vs (listof contract?)]
      
      (: and/c.2 : -φ ℓ -V^ -V^ → (Values -V^ -φ))
      (define (and/c.2 φ ℓ V₁ V₂)
        (define α₁ (mk-α (-α.and/c-l ℓ H)))
        (define α₂ (mk-α (-α.and/c-r ℓ H)))
        (define ℓ₁ (ℓ-with-id ℓ 'left-conj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-conj))
        (define C (-And/C (and (C^-flat? V₁) (C^-flat? V₂)) (αℓ α₁ ℓ₁) (αℓ α₂ ℓ₂)))
        (values {set C} (alloc Σ (alloc Σ φ α₁ V₁) α₂ V₂)))
      (reduce-contracts 'and/c ℓ₀ H φ Σ Vs ⟦k⟧ and/c.2 (list {set 'any/c}))))

  (def (not/c W ℓ Φ^ Ξ Σ)
    #:init ([V flat-contract?])
    (define α (mk-α (-α:not/c ℓ (Ξ:co-ctx Ξ))))
    (define ℓ* (ℓ-with-id ℓ 'not/c))
    {set (ret! (V->R (Not/C (αℓ α ℓ*)) Φ^) Ξ Σ)})
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
    {set (ret! (V->R (One-Of/C vals) Φ^) Ξ Σ)})
  #;[symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
  (def (vectorof W ℓ Φ^ Ξ Σ) ; FIXME uses
    #:init ([V contract?])
    (define α (mk-α (-α:vectof ℓ (Ξ:co-ctx Ξ))))
    {set (ret! (V->R (Vectof (αℓ α (ℓ-with-id ℓ 'vectorof))) Φ^) Ξ Σ)})
  (def vector-immutableof (contract? . -> . contract?))
  (def (vector/c W ℓ₀ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof contract?)]
    (define H (Ξ:co-ctx Ξ))
    ; FIXME uses ; FIXME check for domains to be listof contract
    (define αℓs : (Listof αℓ) ; with side-effect allocating
      (for/list ([Vᵢ (in-list W)] [i (in-naturals)] #:when (index? i))
        (define αᵢ (mk-α (-α:vect/c ℓ₀ H i)))
        (⊔ᵥ! Σ αᵢ Vᵢ)
        (αℓ αᵢ (ℓ-with-id ℓ₀ i))))
    {set (ret! (V->R (Vect/C αℓs) Φ^) Ξ Σ)})
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
    (⊔ᵥ! Σ αₗ Disj)
    (⊔ᵥ! Σ α₁ Cons)
    (⊔ᵥ! Σ αₕ C)
    (⊔ᵥ! Σ αₜ Ref)
    {set (ret! (V->R Ref Φ^) Ξ Σ)})
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
