#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/contract
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         "def-prim.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.1 Data-structure Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-prim/todo flat-named-contract ; FIXME uses
 (any/c flat-contract? . -> . flat-contract?))
(def-prim/custom (any/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  #:domain ([W any/c])
  {set (-ΓA Γ (-W -True/Vs -tt))})
(def-prim/custom (none/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  #:domain ([W any/c])
  {set (-ΓA Γ (-W -False/Vs -ff))})
(def-prim/custom (or/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  #:domain ([W₁ contract?] [W₂ contract?]) ; FIXME uses
  (match-define (-Σ σ _ _) Σ)
  (match-define (-W¹ V₁ s₁) W₁)
  (match-define (-W¹ V₂ s₂) W₂)
  (define α₁ (-α->-⟪α⟫ (or (keep-if-const s₁) (-α.or/c-l ℓ ⟪ℋ⟫))))
  (define α₂ (-α->-⟪α⟫ (or (keep-if-const s₂) (-α.or/c-r ℓ ⟪ℋ⟫))))
  (σ⊕*! σ [α₁ ↦ V₁] [α₂ ↦ V₂])
  (define ℓ₁ (+ℓ/ctc ℓ 0))
  (define ℓ₂ (+ℓ/ctc ℓ 1))
  (define C (-Or/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))
  {set (-ΓA Γ (-W (list C) (-?@ 'or/c s₁ s₂)))})
(def-prim/custom (and/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  #:domain ([W₁ contract?] [W₂ contract?]) ; FIXME uses
  (match-define (-Σ σ _ _) Σ)
  (match-define (-W¹ V₁ s₁) W₁)
  (match-define (-W¹ V₂ s₂) W₂)
  (define α₁ (-α->-⟪α⟫ (or (keep-if-const s₁) (-α.and/c-l ℓ ⟪ℋ⟫))))
  (define α₂ (-α->-⟪α⟫ (or (keep-if-const s₂) (-α.and/c-r ℓ ⟪ℋ⟫))))
  (σ⊕*! σ [α₁ ↦ V₁] [α₂ ↦ V₂])
  (define ℓ₁ (+ℓ/ctc ℓ 0))
  (define ℓ₂ (+ℓ/ctc ℓ 1))
  (define C (-And/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))
  {set (-ΓA Γ (-W (list C) (-?@ 'and/c s₁ s₂)))})
(def-prim/custom (not/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  #:domain ([W flat-contract?])
  (match-define (-Σ σ _ _) Σ)
  (match-define (-W¹ V s) W)
  (define α (-α->-⟪α⟫ (or (keep-if-const s) (-α.not/c ℓ ⟪ℋ⟫))))
  (σ⊕! σ α V)
  (define ℓ* (+ℓ/ctc ℓ 0))
  (define C (-Not/C (cons α ℓ*)))
  {set (-ΓA Γ (-W (list C) (-?@ 'not/c s)))})
(def-prim/todo =/c  (real? . -> . flat-contract?))
(def-prim/todo </c  (real? . -> . flat-contract?))
(def-prim/todo >/c  (real? . -> . flat-contract?))
(def-prim/todo <=/c (real? . -> . flat-contract?))
(def-prim/todo >=/c (real? . -> . flat-contract?))
(def-prim/todo between/c (real? real? . -> . flat-contract?))
[def-alias real-in between/c]
(def-prim/todo integer-in (exact-integer? exact-integer? . -> . flat-contract?))
(def-prim/todo char-in (char? char? . -> . flat-contract?))
(def-prim/todo def-alias natural-number/c exact-nonnegative-integer?)
(def-prim/todo string-len/c (real? . -> . flat-contract?))
(def-alias false/c not)
(def-pred printable/c)
#;[one-of/c
   (() #:rest (listof flat-contract?) . ->* . contract?)]
#;[symbols
   (() #:rest (listof symbol?) . ->* . flat-contract?)]
(def-prim/custom (vectorof ⟪ℋ⟫ ℓ l Σ Γ Ws) ; FIXME uses
  #:domain ([W contract?])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ V s) W)
  (define ⟪α⟫ (-α->-⟪α⟫ (or (keep-if-const s) (-α.vectorof ℓ ⟪ℋ⟫))))
  (σ⊕! σ ⟪α⟫ V)
  (define ℓ* (+ℓ/ctc ℓ 0))
  (define C (-Vectorof (cons ⟪α⟫ ℓ*)))
  {set (-ΓA Γ (-W (list C) (-?@ 'vectorof s)))})
(def-prim/todo vector-immutableof (contract? . -> . contract?))
(def-prim/custom (vector/c ⟪ℋ⟫ ℓ l Σ Γ Ws)
  ; FIXME uses ; FIXME check for domains to be listof contract
  (define σ (-Σ-σ Σ))
  (define-values (αs ℓs ss) ; with side effect widening store
    (for/lists ([αs : (Listof -⟪α⟫)] [ℓs : (Listof -ℓ)] [ss : (Listof -s)])
               ([W (in-list Ws)] [i (in-naturals)] #:when (index? i))
      (match-define (-W¹ V s) W)
      (define ⟪α⟫ (-α->-⟪α⟫ (or (keep-if-const s) (-α.vector/c ℓ ⟪ℋ⟫ i))))
      (define ℓ : -ℓ (+ℓ/ctc ℓ i))
      (σ⊕! σ ⟪α⟫ V)
      (values ⟪α⟫ ℓ s)))
  (define C (-Vector/C (map (inst cons -⟪α⟫ -ℓ) αs ℓs)))
  {set (-ΓA Γ (-W (list C) (apply -?@ 'vector/c ss)))})
#;[vector-immutable/c
   (() #:rest (listof contract?) . ->* . contract?)]
(def-prim/todo box/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo box-immutable/c (contract? . -> . contract?))
(def-prim/todo listof (contract? . -> . list-contract?))
(def-prim/todo non-empty-listof (contract? . -> . list-contract?))
(def-prim/todo list*of (contract? . -> . contract?))
(def-prim/todo cons/c (contract? contract? . -> . contract?))
#;[list/c
   (() #:rest (listof contract?) . ->* . list-contract?)]
(def-prim/todo syntax/c (flat-contract? . -> . flat-contract?))
(def-prim/todo parameter/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo procedure-arity-includes/c
 (exact-nonnegative-integer? . -> . flat-contract?))
(def-prim/todo hash/c ; FIXME uses
 (chaperone-contract? contract? . -> . contract?))
(def-prim/todo channel/c (contract? . -> . contract?))
(def-prim/todo continuation-mark-key/c (contract? . -> . contract?))
;;[evt/c (() #:rest (listof chaperone-contract?) . ->* . chaperone-contract?)]
(def-prim/todo promise/c (contract? . -> . contract?))
(def-prim/todo flat-contract ((any/c . -> . any/c) . -> . flat-contract?))
(def-prim/todo flat-contract-predicate (flat-contract? . -> . (any/c . -> . any/c)))

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
(def-prim contract-first-order-passes?
 (contract? any/c . -> . boolean?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred contract?)
(def-pred chaperone-contract?)
(def-pred impersonator-contract?)
(def-pred flat-contract?)
(def-pred list-contract?)
(def-prim/todo contract-name (contract? . -> . any/c))
(def-prim/todo value-contract (has-contract? . -> . (or/c contract? not)))
[def-pred has-contract?]
(def-prim/todo value-blame (has-blame? . -> . (or/c blame? not)))
[def-pred has-blame?]
(def-prim/todo contract-projection (contract? . -> . (blame? . -> . (any/c . -> . any/c))))
(def-prim/todo make-none/c (any/c . -> . contract?))
(def-opq contract-continuation-mark-key continuation-mark-key?)
