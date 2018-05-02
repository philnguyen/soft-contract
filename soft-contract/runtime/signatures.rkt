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

(#|State sans store|# Ξ . ::= . (Ξ:co [frames : K]
                                      [mark : (Option (Pairof Ctx M))]
                                      [ctx : H])
                                Blm)
(#|Local kont.     |# K . ::= . (K [init : (Listof F)] [rest : αₖ]))
(#|Instrumentation |# -H . ::= . #:TBD)
(#|Stack address   |# αₖ . ::= . (αₖ:clo ⟦E⟧ Ρ)
                                 (αₖ:hv HV-Tag)
                                 (αₖ:term/c α W))
(#|Value address   |# -α . ::= . #:TBD) 
(#|Result          |# R . ::= . (R W Φ^))
(#|Path            |# Φ . ::= . (Φ [alias : $] [condition : Ψ]))
(#|Path alias      |# $ . ≜ . (Immutable-HashTable Symbol S))
(#|Path condition  |# Ψ . ≜ . (Immutable-HashTable (Listof S) (℘ P)))
(#|Environment     |# Ρ . ≜ . (Immutable-HashTable Symbol α))
(struct Σ ([val : Σᵥ] [kon : Σₖ] [evl : Σₐ]) #:transparent #:mutable)
#;(#|Store           |# Σ  . ::= . (Σ [val : Σᵥ] [kon : Σₖ] [evl : Σₐ]) #:mutable)
(#|Value store     |# Σᵥ . ≜ . (Immutable-HashTable α V^))
(#|Kont. store     |# Σₖ . ≜ . (Immutable-HashTable αₖ Ξ:co^))
(#|Eval. store     |# Σₐ . ≜ . (Immutable-HashTable Ξ:co R^))
(#|Call history    |# M  . ≜ . (Immutable-HashTable Clo Call-Record))
(#|Value list      |# W  . ≜ . (Listof T^))
(#|Sym/Abs value   |# T  . ::= . S V)
(#|Compiled expr   |# ⟦E⟧ . ≜ . (  Ρ Φ^ Ξ:co Σ → Ξ))
(#|Application     |# ⟦F⟧ . ≜ . (W ℓ Φ^ Ξ:co Σ → Ξ))
(#|Call graph      |# CG . ≜ . (Immutable-HashTable αₖ (℘ αₖ))) ; FIXME obsolete
(#|Kont. frame     |# F . ::= . #:TBD)
;; Approximated versions of things
(Φ^ . ≜ . (℘ Φ))
(V^ . ≜ . (℘ V))
(T^ . ≜ . (℘ T))
(R^ . ≜ . (℘ R))
(Ξ:co^ . ≜ . (℘ Ξ:co))
(W^ . ≜ . (℘ W))
(⟦F⟧^ . ≜ . (W ℓ Φ^ Ξ:co Σ → (℘ Ξ)))
(?R . ≜ . (Option R))
(Call-Record . ::= . (Call-Record [last-args : W] [sc-graph : SCG]))
(#|Size-change Graph|# SCG . ≜ . (Immutable-HashTable (Pairof Integer Integer) Ch))
(Ch . ::= . '↓ '↧)

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
                     P #|hack in prim DSL|#) 
(#|Symbolic value|# S . ::= . -b (S:clo -formals ⟦E⟧ Ρ) (S:α α) (S:@ S (Listof S)))
(#|Predicates|# P . ::= . -o (P:≤ Real) (P:< Real) (P:≥ Real) (P:> Real) (P:≡ Base) (P:¬ P) (P:arity-includes Index))

(#|Non-primitive function|# Fn . ::= . (Clo -formals ⟦E⟧ Ρ)
                                       (Case-Clo (Listof Clo))
                                       (Fn:● Arity HV-Tag))

(#|Contract|# C . ::= . (And/C [flat? : Boolean] αℓ αℓ)
                        (Or/C [flat? : Boolean] αℓ αℓ)
                        (Not/C αℓ)
                        (One-Of/C (Listof Base))
                        (X/C α)
                        Prox/C
                        (Seal/C Symbol H -l))
(#|Proxies|# Prox/C . ::= . Fn/C
                            (St/C [flat? : Boolean] -𝒾 (Listof αℓ))
                            (Vectof αℓ)
                            (Vect/C (Listof αℓ))
                            (Hash/C [key : αℓ] [val : αℓ])
                            (Set/C [elems : αℓ]))
(#|Func. contract|# Fn/C . ::= . (==> [doms : (-var αℓ)] [rng : (Option (Listof αℓ))])
                                 (==>i [doms : (Listof Dom)] [mk-rng : Dom])
                                 (∀/C (Listof Symbol) ⟦E⟧ Ρ)
                                 (Case-=> (Listof ==>))
                                 'scv:terminating/c)

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
(#|Context tag for havoc|# HV-Tag . ≜ . (HV-Tag (Option -l) H) #:ad-hoc)
(#|Monitor context|# Ctx . ::= . (Ctx [pos : -l] [neg : -l] [src : -l] [loc : ℓ]))
(Cardinality . ::= . 0 1 'N)
(Dec . ::= . '✓ '✗)
(?Dec . ≜ . (Option Dec))

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
    (syntax-rules () [(_ α) (X/G _ (St/C _ (== St-id) _) α)])))
(define-St-matcher (Cons αₕ αₜ) -𝒾-cons)
(define-St/G-matcher Cons/G -𝒾-cons)
(define-St-matcher (Box α) -𝒾-box)
(define-St/G-matcher Box/G -𝒾-box)


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
   [Σᵥ@/ctx : (Σ Ctx αℓ → (Values V^ Ctx))]
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
   [C-flat? : (T → Boolean)]
   [C^-flat? : (T^ → Boolean)]
   [with-negative-party : (-l V → V)]
   [with-positive-party : (-l V → V)]
   [behavioral? : (Σᵥ V → Boolean)]
   [guard-arity : (case->
                   [==> → Arity]
                   [Fn/C → (Option Arity)])]
   [blm-arity : (ℓ -l Arity W → Blm)]
   [T⊔ : (T^ T^ → T^)]
   [T⊔₁ : (T^ T → T^)]
   [V⊔₁ : (V^ V → V^)]
   [V⊔ : (V^ V^ → V^)]
   [⊥T : T^]
   [collapse-value-lists : (W^ Natural → W)]
   [K+ : (F Ξ:co → Ξ:co)]
   #;[estimate-list-lengths : (Σᵥ V → (℘ (U #f Arity)))]
   ))

(define-signature evl^
  ([⊤Φ : Φ]
   [⊥Φ^ : Φ^]
   [Φ@ : (Φ (Listof T) → (℘ P))]
   [R⊔ : (R R → R)]
   [R⊔₁ : (R (Listof T) Φ → R)]
   [validate-R : (?R → ?R)]
   [T->R : ((U T T^) Φ^ → R)]
   [filter/arity : (R^ Natural → (Values R^ W^))]
   [collapse-R^ : (R^ → (Values W^ Φ^))] 
   [collapse-R^-1 : (R^ → (Values T^ Φ^))]
   [collapse-R^/Φ^ : (R^ → Φ^)]
   [collapse-R^/W^ : (R^ → W^)] 
   [with-2-paths : (∀ (X) (→ (Values R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X))]
   [with-3-paths : (∀ (X) (→ (Values R^ R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X))]
   [with-2-paths/collapse : (∀ (X) (→ (Values R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X))]
   [with-3-paths/collapse : (∀ (X) (→ (Values R^ R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X))]))

(define-signature pretty-print^
  ([show-blm-reason : ((U V P V^) → Sexp)]
   [show-T^ : (T^ → Sexp)])) 
