#lang typed/racket/base

(provide prims-08@)

(require racket/match
         racket/set
         racket/contract
         racket/splicing
         typed/racket/unit
         set-extras
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "def.rkt"
         "signatures.rkt")

(define-unit prims-08@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^ pretty-print^)
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
      
      ((: reduce-contracts : -l ℓ -$ -H -Σ -Γ (Listof -W¹) -⟦k⟧ (ℓ -W¹ -W¹ → (Values -V -?t)) -W → (℘ -ς))
       (define (reduce-contracts lo ℓ $ H Σ Γ Ws ⟦k⟧ comb id)
         (match Ws
           ['() (⟦k⟧ id $ Γ H Σ)]
           [_
            (define-values (V* t*)
              (let loop : (Values -V -?t) ([Ws : (Listof -W¹) Ws] [i : Natural 0])
                   (match Ws
                     [(list (-W¹ V t)) (values V t)]
                     [(cons Wₗ Wsᵣ)
                      (define-values (Vᵣ tᵣ) (loop Wsᵣ (+ 1 i)))
                      (comb (ℓ-with-id ℓ i) Wₗ (-W¹ Vᵣ tᵣ))])))
            (⟦k⟧ (-W (list V*) t*) $ Γ H Σ)])))
    
    (def (or/c ℓ₀ Ws $ Γ H Σ ⟦k⟧)
      #:init ()
      #:rest (Ws (listof contract?))
      (: or/c.2 : ℓ -W¹ -W¹ → (Values -V -?t))
      (define (or/c.2 ℓ W₁ W₂)
        (match-define (-W¹ V₁ t₁) W₁)
        (match-define (-W¹ V₂ t₂) W₂)
        (define α₁ (-α->⟪α⟫ (-α.or/c-l ℓ H)))
        (define α₂ (-α->⟪α⟫ (-α.or/c-r ℓ H)))
        (σ⊕V! Σ α₁ V₁)
        (σ⊕V! Σ α₂ V₂)
        (define ℓ₁ (ℓ-with-id ℓ 'left-disj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-disj))
        (define C (-Or/C (and (C-flat? V₁) (C-flat? V₂)) (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)))
        (values C (?t@ 'or/c t₁ t₂)))
      (reduce-contracts 'or/c ℓ₀ $ H Σ Γ Ws ⟦k⟧ or/c.2 (+W (list 'none/c))))
    
    (def (and/c ℓ₀ Ws $ Γ H Σ ⟦k⟧)
      #:init ()
      #:rest (Ws (listof contract?))
      
      (: and/c.2 : ℓ -W¹ -W¹ → (Values -V -?t))
      (define (and/c.2 ℓ W₁ W₂)
        (match-define (-W¹ V₁ t₁) W₁)
        (match-define (-W¹ V₂ t₂) W₂)
        (define α₁ (-α->⟪α⟫ (-α.and/c-l ℓ H)))
        (define α₂ (-α->⟪α⟫ (-α.and/c-r ℓ H)))
        (σ⊕V! Σ α₁ V₁)
        (σ⊕V! Σ α₂ V₂)
        (define ℓ₁ (ℓ-with-id ℓ 'left-conj))
        (define ℓ₂ (ℓ-with-id ℓ 'right-conj))
        (define C (-And/C (and (C-flat? V₁) (C-flat? V₂)) (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)))
        (values C (?t@ 'and/c t₁ t₂)))
      (reduce-contracts 'and/c ℓ₀ $ H Σ Γ Ws ⟦k⟧ and/c.2 (+W (list 'any/c)))))

  (def (not/c ℓ Ws $ Γ H Σ ⟦k⟧)
    #:init ([W flat-contract?])
    (match-define (-W¹ V t) W)
    (define α (-α->⟪α⟫ (-α.not/c ℓ H)))
    (σ⊕V! Σ α V)
    (define ℓ* (ℓ-with-id ℓ 'not/c))
    (define C (-Not/C (-⟪α⟫ℓ α ℓ*)))
    (⟦k⟧ (-W (list C) (?t@ 'not/c t)) $ Γ H Σ))
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
  (def (one-of/c ℓ Ws $ Γ H Σ ⟦k⟧)
    #:init ()
    #:rest (Ws (listof any/c))
    (define-values (vals ts.rev)
      (for/fold ([vals : (℘ Base) ∅] [ts : (Listof -?t) '()])
                ([W (in-list Ws)] [i (in-naturals)])
        (match W
          [(-W¹ (-b b) t) (values (set-add vals b) (cons t ts))]
          [W (error 'one-of/c
                    "only support simple values for now, got ~a at ~a~a position"
                    (show-W¹ W) i (case i [(1) 'st] [(2) 'nd] [else 'th]))])))
    (define Wₐ (-W (list (-One-Of/C vals)) (apply ?t@ 'one-of/c (reverse ts.rev))))
    (⟦k⟧ Wₐ $ Γ H Σ))
  #;[symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
  (def (vectorof ℓ Ws $ Γ H Σ ⟦k⟧) ; FIXME uses
    #:init ([W contract?])
    (match-define (-W¹ V t) W)
    (define ⟪α⟫ (-α->⟪α⟫ (-α.vectorof ℓ H)))
    (σ⊕V! Σ ⟪α⟫ V)
    (define C (-Vectorof (-⟪α⟫ℓ ⟪α⟫ (ℓ-with-id ℓ 'vectorof))))
    (⟦k⟧ (-W (list C) (?t@ 'vectorof t)) $ Γ H Σ))
  (def vector-immutableof (contract? . -> . contract?))
  (def (vector/c ℓ₀ Ws $ Γ H Σ ⟦k⟧)
    #:init ()
    #:rest (Ws (listof contract?))
    ; FIXME uses ; FIXME check for domains to be listof contract
    (define-values (αs ℓs ss) ; with side effect widening store
      (for/lists ([αs : (Listof ⟪α⟫)] [ℓs : (Listof ℓ)] [ts : (Listof -?t)])
                 ([W (in-list Ws)] [i (in-naturals)] #:when (index? i))
        (match-define (-W¹ V t) W)
        (define ⟪α⟫ (-α->⟪α⟫ (-α.vector/c ℓ₀ H i)))
        (σ⊕V! Σ ⟪α⟫ V)
        (values ⟪α⟫ (ℓ-with-id ℓ₀ i) t)))
    (define C (-Vector/C (map -⟪α⟫ℓ αs ℓs)))
    (⟦k⟧ (-W (list C) (apply ?t@ 'vector/c ss)) $ Γ H Σ))
  #;[vector-immutable/c
     (() #:rest (listof contract?) . ->* . contract?)]
  (def box/c ; FIXME uses
    (contract? . -> . contract?))
  (def box-immutable/c (contract? . -> . contract?))
  (def (listof ℓ Ws $ Γ H Σ ⟦k⟧)
    #:init ([W contract?])
    (match-define (-W¹ C c) W)
    (define flat? (C-flat? C))
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
    (σ⊕V! Σ αₗ Disj)
    (σ⊕V! Σ α₁ Cons)
    (σ⊕V! Σ αₕ C)
    (σ⊕V! Σ αₜ Ref)
    (⟦k⟧ (-W (list Ref) (?t@ 'listof c)) $ Γ H Σ))
  (def non-empty-listof (contract? . -> . list-contract?))
  (def list*of (contract? . -> . contract?))
  (def cons/c (contract? contract? . -> . contract?))
  (def list/c (() #:rest (listof contract?) . ->* . list-contract?))
  (def syntax/c (flat-contract? . -> . flat-contract?))
  (def parameter/c ; FIXME uses
    (contract? . -> . contract?))
  (def procedure-arity-includes/c
    (exact-nonnegative-integer? . -> . flat-contract?))
  (def (hash/c ℓ Ws $ Γ H Σ ⟦k⟧) ; FIXME uses
    #:init ([Wₖ contract?] [Wᵥ contract?])
    (match-define (-W¹ _ tₖ) Wₖ)
    (match-define (-W¹ _ tᵥ) Wᵥ)
    (define αₖ (-α->⟪α⟫ (-α.hash/c-key ℓ H)))
    (define αᵥ (-α->⟪α⟫ (-α.hash/c-val ℓ H)))
    (σ⊕! Σ Γ αₖ Wₖ)
    (σ⊕! Σ Γ αᵥ Wᵥ)
    (define V (-Hash/C (-⟪α⟫ℓ αₖ (ℓ-with-id ℓ 'hash/c.key)) (-⟪α⟫ℓ αᵥ (ℓ-with-id ℓ 'hash/c.val))))
    (⟦k⟧ (-W (list V) (?t@ 'hash/c tₖ tᵥ)) $ Γ H Σ))
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
