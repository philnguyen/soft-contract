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
         "../proof-relation/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "def.rkt"
         "signatures.rkt")

(define-unit prims-08@
  (import prim-runtime^ proof-system^ widening^ val^ path^ sto^ pretty-print^)
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
        (define α₁ (-α->⟪α⟫ (-α.or/c-l ℓ H)))
        (define α₂ (-α->⟪α⟫ (-α.or/c-r ℓ H)))
        (define ℓ₁ (ℓ-with-id ℓ 'left-disj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-disj))
        (define C (-Or/C (and (C^-flat? V₁) (C^-flat? V₂)) (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)))
        (values {set C} (φ⊔ (φ⊔ φ α₁ V₁) α₂ V₂)))
      (reduce-contracts 'or/c ℓ₀ H φ Σ Vs ⟦k⟧ or/c.2 (list {set 'none/c})))
    
    (def (and/c ℓ₀ Vs H φ Σ ⟦k⟧)
      #:init ()
      #:rest [Vs (listof contract?)]
      
      (: and/c.2 : -φ ℓ -V^ -V^ → (Values -V^ -φ))
      (define (and/c.2 φ ℓ V₁ V₂)
        (define α₁ (-α->⟪α⟫ (-α.and/c-l ℓ H)))
        (define α₂ (-α->⟪α⟫ (-α.and/c-r ℓ H)))
        (define ℓ₁ (ℓ-with-id ℓ 'left-conj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-conj))
        (define C (-And/C (and (C^-flat? V₁) (C^-flat? V₂)) (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)))
        (values {set C} (φ⊔ (φ⊔ φ α₁ V₁) α₂ V₂)))
      (reduce-contracts 'and/c ℓ₀ H φ Σ Vs ⟦k⟧ and/c.2 (list {set 'any/c}))))

  (def (not/c ℓ Vs H φ Σ ⟦k⟧)
    #:init ([V flat-contract?])
    (define α (-α->⟪α⟫ (-α.not/c ℓ H)))
    (define ℓ* (ℓ-with-id ℓ 'not/c))
    (⟦k⟧ (list {set (-Not/C (-⟪α⟫ℓ α ℓ*))}) H (φ⊔ φ α V) Σ))
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
  (def (one-of/c ℓ Vs H φ Σ ⟦k⟧)
    #:init ()
    #:rest [Vs (listof any/c)]
    (define vals
      (for/fold ([vals : (℘ Base) ∅]) ([V (in-list Vs)])
        (match V
          [(singleton-set (-b b)) (set-add vals b)]
          [V (error 'one-of/c
                    "only support simple values for now, got ~a"
                    V)])))
    (⟦k⟧ (list {set (-One-Of/C vals)}) H φ Σ))
  #;[symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
  (def (vectorof ℓ Vs H φ Σ ⟦k⟧) ; FIXME uses
    #:init ([V contract?])
    (define α (-α->⟪α⟫ (-α.vectorof ℓ H)))
    (⟦k⟧ (list {set (-Vectorof (-⟪α⟫ℓ α (ℓ-with-id ℓ 'vectorof)))}) H (φ⊔ φ α V) Σ))
  (def vector-immutableof (contract? . -> . contract?))
  (def (vector/c ℓ₀ Vs H φ Σ ⟦k⟧)
    #:init ()
    #:rest [Vs (listof contract?)]
    ; FIXME uses ; FIXME check for domains to be listof contract
    (define-values (αs-rev ℓs-rev φ*) ; with side effect widening store
      (for/fold ([αs-rev : (Listof ⟪α⟫) '()] [ℓs-rev : (Listof ℓ) '()] [φ : -φ φ])
                ([Vᵢ (in-list Vs)] [i (in-naturals)] #:when (index? i))
        (define αᵢ (-α->⟪α⟫ (-α.vector/c ℓ₀ H i)))
        (values (cons αᵢ αs-rev)
                (cons (ℓ-with-id ℓ₀ i) ℓs-rev)
                (φ⊔ φ αᵢ Vᵢ))))
    (define C (-Vector/C (reverse (map -⟪α⟫ℓ αs-rev ℓs-rev))))
    (⟦k⟧ (list {set C}) H φ* Σ))
  #;[vector-immutable/c
     (() #:rest (listof contract?) . ->* . contract?)]
  (def box/c ; FIXME uses
    (contract? . -> . contract?))
  (def box-immutable/c (contract? . -> . contract?))
  (def (listof ℓ Vs H φ Σ ⟦k⟧)
    #:init ([C contract?])
    (define flat? (C^-flat? C))
    (define α₀ (-α->⟪α⟫ (-α.imm 'null?)))
    (define α₁ (-α->⟪α⟫ (-α.or/c-r ℓ H)))
    (define αₕ (-α->⟪α⟫ (-α.struct/c -𝒾-cons ℓ H 0)))
    (define αₜ (-α->⟪α⟫ (-α.struct/c -𝒾-cons ℓ H 1)))
    (define αₗ (-α->⟪α⟫ (-α.x/c (+x!/memo 'listof ℓ) H)))
    (define ℓ₀ (ℓ-with-id ℓ 'null?))
    (define ℓ₁ (ℓ-with-id ℓ 'pair?))
    (define ℓₕ (ℓ-with-id ℓ 'elem))
    (define ℓₜ (ℓ-with-id ℓ 'rest))
    (define Disj (-Or/C flat? (-⟪α⟫ℓ α₀ ℓ₀) (-⟪α⟫ℓ α₁ ℓ₁)))
    (define Cons (-St/C flat? -𝒾-cons (list (-⟪α⟫ℓ αₕ ℓₕ) (-⟪α⟫ℓ αₜ ℓₜ))))
    (define Ref (-x/C αₗ))
    (define φ* (φ⊔ (φ⊔ (φ⊔ (φ⊔ φ αₗ Disj) α₁ Cons) αₕ C) αₜ Ref))
    (⟦k⟧ (list {set Ref}) H φ* Σ))
  (def non-empty-listof (contract? . -> . list-contract?))
  (def list*of (contract? . -> . contract?))
  (def cons/c (contract? contract? . -> . contract?))
  (def list/c (() #:rest (listof contract?) . ->* . list-contract?))
  (def syntax/c (flat-contract? . -> . flat-contract?))
  (def parameter/c ; FIXME uses
    (contract? . -> . contract?))
  (def procedure-arity-includes/c
    (exact-nonnegative-integer? . -> . flat-contract?))
  (def (hash/c ℓ Vs H φ Σ ⟦k⟧) ; FIXME uses
    #:init ([Vₖ contract?] [Vᵥ contract?])
    (define αₖ (-α->⟪α⟫ (-α.hash/c-key ℓ H)))
    (define αᵥ (-α->⟪α⟫ (-α.hash/c-val ℓ H)))
    (define φ* (φ⊔ (φ⊔ φ αₖ Vₖ) αᵥ Vᵥ))
    (define V (-Hash/C (-⟪α⟫ℓ αₖ (ℓ-with-id ℓ 'hash/c.key)) (-⟪α⟫ℓ αᵥ (ℓ-with-id ℓ 'hash/c.val))))
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
