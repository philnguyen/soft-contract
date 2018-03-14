#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         bnf
         unreachable
         intern
         set-extras
         "../utils/bijection.rkt"
         "../ast/signatures.rkt"
         )

(#|State sans store|# Ξ . ::= . (Ξ:co [kon : K] [ret : αₖ] [ctx : H])
                                Blm)
(#|Local kont.     |# K . ≜ . (Listof F))
(#|Instrumentation |# -H . ::= . #:TBD)
(#|Stack address   |# αₖ . ::= . (αₖ ⟦E⟧ Ρ))
(#|Value address   |# -α . ::= . #:TBD) 
(#|Result          |# R . ::= . (R W^ Φ^))
(#|Path-condition  |# Φ . ≜ . (℘ S))
(#|Environment     |# Ρ  . ≜ . (Immutable-HashTable Symbol α))
(struct Σ ([val : Σᵥ] [kon : Σₖ] [evl : Σₐ]) #:transparent #:mutable)
#;(#|Store           |# Σ  . ::= . (Σ [val : Σᵥ] [kon : Σₖ] [evl : Σₐ]) #:mutable)
(#|Value store     |# Σᵥ . ≜ . (Immutable-HashTable α V^))
(#|Kont. store     |# Σₖ . ≜ . (Immutable-HashTable αₖ Ξ:co^))
(#|Eval. store     |# Σₐ . ≜ . (Immutable-HashTable Ξ:co R^))
(#|Value list      |# W  . ≜ . (Listof V^))
(#|Compiled expr   |# ⟦E⟧ . ≜ . (  Ρ Φ^ Ξ:co Σ → Ξ))
(#|Application     |# ⟦F⟧ . ≜ . (W ℓ Φ^ Ξ:co Σ → Ξ))
(#|Call graph      |# CG . ≜ . (Immutable-HashTable αₖ (℘ αₖ)))
(#|Kont. frame     |# F . ::= . #:TBD)
;; Approximated versions of things
(Φ^ . ≜ . (℘ Φ))
(V^ . ≜ . (℘ V))
(R^ . ≜ . (℘ R))
(Ξ:co^ . ≜ . (℘ Ξ:co))
(W^ . ≜ . (℘ W))
(⟦F⟧^ . ≜ . (W ℓ Φ^ Ξ:co Σ → (℘ Ξ)))

(#|Value|# V . ::= . (-● (℘ P))
                     -prim
                     (St -𝒾 (Listof α))
                     (Vect (Listof α))
                     (Vect^ [content : α] [length : V^])
                     (Hash^ [key : α] [val : α] [immut? : Boolean])
                     (Set^ [elems : α] [bimmut? : Boolean])
                     Fn
                     (X/G [ctx : Ctx] [guard : Prox/C] [val : α])
                     (Sealed α)
                     C
                     S)
(#|Proxies|# Prox/C . ::= . Fn/C St/C Vect/C Hash/C Set/C)
(#|Symbolic value|# S . ::= . -b (S:α α) (S:@ -o (Listof S)))
(#|Predicates|# P . ::= . -o (P:Le S) (P:Lt S) (P:Ge S) (P:Gt S) (P:Neg P))

(#|Non-primitive function|# Fn . ::= . (Clo -formals ⟦E⟧ Ρ)
                                       (Case-Clo (Listof Clo))
                                       (Fn:● Arity HV-Tag))

(#|Contract|# C . ::= . (And/C [flat? : Boolean] αℓ αℓ)
                        (Or/C [flat? : Boolean] αℓ αℓ)
                        (Not/C αℓ)
                        (One-Of/C (Listof Base))
                        (X/C α)
                        Fn/C
                        (St/C [flat? : Boolean] -𝒾 (Listof αℓ))
                        (Vectof αℓ)
                        (Vect/C (Listof αℓ))
                        (Hash/C [key : αℓ] [val : αℓ])
                        (Set/C [elems : αℓ])
                        (Seal/C Symbol H -l))

(#|Func. contract|# Fn/C . ::= . (==> [doms : (-maybe-var αℓ)] [rng : (Option (Listof αℓ))])
                                 (==>i [doms : (Listof Dom)] [mk-rng : Dom])
                                 (∀/C (Listof Symbol) ⟦E⟧ Ρ)
                                 (Case-=> (Listof Fn/C)))

(#|Strict -> |# struct ==>/⇓  ==> () #:transparent)
(#|Strict ->i|# struct ==>i/⇓ ==> () #:transparent)
(#|Blame|# Blm . ::= . (Blm [violator : ℓ]
                            [origin : -l]
                            [ctc : (Listof (U V P V^))]
                            [val : W]))
(#|Contract field access|# αℓ . ::= . (αℓ α ℓ))
(#|Named domain|# Dom . ::= . (Dom [name : Symbol] [ctc : (U Clo α)] [src : ℓ]))
(#|Compiled domain|# ⟦dom⟧ . ::= . (⟦dom⟧ [name : Symbol]
                                          [dependency : (Option (Listof Symbol))]
                                          [ctx : ⟦E⟧]
                                          [src : ℓ]))
(#|Context tag for havoc|# HV-Tag . ::= . '† [#:reuse (Pairof -l H)])
(#|Monitor context|# Ctx . ::= . (Ctx [pos : -l] [neg : -l] [src : -l] [loc : ℓ]))
(Cardinality . ::= . 0 1 'N)
(Valid . ::= . '✓ '✗ '?)

(define-interner α -α
  #:intern-function-name mk-α
  #:unintern-function-name inspect-α)
(define-interner H -H
  #:intern-function-name mk-H
  #:unintern-function-name inspect-H)

;; Convenient patterns
(define-syntax-rule (define-St-matcher (P α ...) St-id)
  (define-match-expander P
    (syntax-rules () [(_ α ...) (St (== St-id) (list α ...))])
    (syntax-rules () [(_ α ...) (St St-id (list α ...))])))
(define-syntax-rule (define-St/G-matcher P St-id)
  (define-match-expander P
    (syntax-rules () [(_ α) (St/G (St/C _ (== St-id) _) α _)])))
(define-St-matcher (Cons αₕ αₜ) -𝒾-cons)
(define-St/G-matcher Cons/G -𝒾-cons)
(define-St-matcher (Box α) -𝒾-box)
(define-St/G-matcher Box/G -𝒾-box)
(define-syntax-rule (Blm/simp ℓ+ lo C V) (Blm (strip-ℓ ℓ+) lo C V))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Some instantiations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-substructs -α
  ;; tmp hack.
  ;; Only use this in the prim DSL where all values are finite
  ;; with purely syntactic components
  (-α:imm #|restricted|# V)
  ;; indirection for `listof` to keep in-sync with regular listof contracts
  (-α:imm:listof     Symbol #|elem, ok with care|# V ℓ)
  (-α:imm:ref-listof Symbol #|elem, ok with care|# V ℓ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Simple helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Ctx-flip : (Ctx → Ctx)
  (match-lambda
    [(Ctx l+ l- lo ℓ) (Ctx l- l+ lo ℓ)]))
(define Ctx-with-ℓ : (Ctx ℓ → Ctx)
  (match-lambda**
    [((Ctx l+ l- lo _) ℓ) (Ctx l+ l- lo ℓ)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Signatures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-signature sto^
  ([⊥Σ : (→ Σ)]
   [⊥Σᵥ : Σᵥ]
   [⊥Σₖ : Σₖ]
   [⊥Σₐ : Σₐ]
   [Σᵥ@ : ((U Σ Σᵥ) α  → V^)]
   [Σₖ@ : ((U Σ Σₖ) αₖ → Ξ:co^)]
   [Σₐ@ : ((U Σ Σₐ) Ξ:co → R^)]
   [Σᵥ@* : ((U Σ Σᵥ) (Listof α) → W)]
   [α• : α]
   [defined-at? : ((U Σ Σᵥ) α → Boolean)]
   [construct-call-graph : ((U Σ Σₖ) → CG)]
   [⊔ᵥ : (Σᵥ α (U V V^) → Σᵥ)]
   [⊔ₖ : (Σₖ αₖ Ξ:co → Σₖ)]
   [⊔ₐ : (Σₐ Ξ:co (U R R^) → Σₐ)]
   [⊔ₐ! : (Σ Ξ:co (U R R^) → Void)]
   [⊔ᵥ! : (Σ α (U V V^) → Void)]
   [⊔ᵥ*! : (Σ (Listof α) (Listof V^) → Void)]
   [⊔ₖ! : (Σ αₖ Ξ:co → Void)]
   ;; Old
   #;[alloc-rest-args : ([-Σ ℓ -H -φ (Listof -V^)] [#:end -V] . ->* . (Values -V -φ))]
   #;[unalloc : (-σ -δσ -V → (℘ (Listof -V^)))]
   #;[unalloc-prefix : (-σ -δσ -V Natural → (℘ (Pairof (Listof -V^) -V)))]
   #;[cardinality : (-σ -δσ ⟪α⟫ → Cardinality)]
   ))

(define-signature env^
  ([⊥Ρ : Ρ]
   [Ρ@ : (Ρ Symbol → α)]
   [Ρ@* : (Ρ (Listof Symbol) → (Listof α))]
   [Ρ+ : (Ρ Symbol α → Ρ)]
   [-x-dummy : Symbol]))


(define-signature val^
  (#;[fresh-sym! : (→ -s)]
   [C-flat? : (V → Boolean)]
   [C^-flat? : (V^ → Boolean)]
   [with-negative-party : (-l V → V)]
   [with-positive-party : (-l V → V)]
   [behavioral? : (Σᵥ V → Boolean)]
   [guard-arity : (Fn/C → Arity)]
   [blm-arity : (ℓ -l Arity W → Blm)]
   [V⊔ : (V^ V^ → V^)]
   [V⊔₁ : (V^ V → V^)]
   [⊥V : V^]
   [collapse-value-lists : (W^ Natural → W)]
   [K+ : (F Ξ:co → Ξ:co)]
   #;[estimate-list-lengths : (Σᵥ V → (℘ (U #f Arity)))]
   ))

(define-signature evl^
  ([V->R : ((U V V^) Φ^ → R)]
   [W->R : ((U W W^) Φ^ → R)]
   [filter/arity : (R^ Natural → (Values R^ W^))]
   [collapse-R^ : (R^ → (Values W^ Φ^))]
   [collapse-R^/Φ^ : (R^ → Φ^)]))

(define-signature pretty-print^
  ([show-blm-reason : ((U V P V^) → Sexp)]
   [show-V^ : (V^ → Sexp)]))
