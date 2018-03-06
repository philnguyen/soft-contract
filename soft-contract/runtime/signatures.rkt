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

(#|State sans store|# Ξ . ::= . (Ξ K H))
(#|Continuation    |# K . ::= . #:TBD)
(#|Instrumentation |# -H . ::= . #:TBD)
(#|Stack address   |# αₖ . ::= . (αₖ ⟦E⟧ Ρ))
(#|Value address   |# -α . ::= . #:TBD)
(#|Compiled expr   |# ⟦E⟧ . ≜ . (Ρ Φ^ K H → Ξ))
(#|Result          |# R . ::= . (R A Φ))
(#|Answer          |# A . ::= . Blm [#:reuse (Listof V^)]) 
(#|Path-condition  |# Φ . ::= . [#:reuse (℘ S)])
(#|Environment     |# Ρ  . ≜ . (Immutable-HashTable Symbol α))
(#|Store           |# Σ  . ::= . (Σ [val : Σᵥ] [kon : Σₖ] [evl : Σₐ]))
(#|Value store     |# Σᵥ . ≜ . (Immutable-HashTable α V^))
(#|Kont. store     |# Σₖ . ≜ . (Immutable-HashTable αₖ K^))
(#|Eval. store     |# Σₐ . ≜ . (Immutable-HashTable K R^))
;; Approximated versions of things
(#|Path-condition^ |# Φ^ . ::= . [#:reuse (℘ Φ)])
(#|Value^          |# V^ . ::= . [#:reuse (℘ V)])
(#|Result^         |# R^ . ::= . [#:reuse (℘ R)])
(#|Kontinuation^   |# K^ . ::= . [#:reuse (℘ K)])

(#|Value|# V . ::= . (-● (℘ P))
                     -prim
                     (St -𝒾 (Listof α))
                     (Vect (Listof α))
                     (Vect^ [content : α] [length : V^])
                     (Hash^ [key : α] [val : α] [immut? : Boolean])
                     (Set^ [elems : α] [immut? : Boolean])
                     Fn
                     X/G
                     (Sealed α))
(#|Guarded value|# struct X/G ([ctx : Ctx] [guard : Prox/C] [val : α]) #:transparent)
(#|Proxies|# Prox/C . ::= . Fn/C St/C Vect/C Hash/C Set/C)
(#|Symbolic value|# S . ::= . (S:α α) (S:@ -o (Listof S)))
(#|Predicates|# P . ::= . #:TBD)

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
                                 (Case=> (Listof Fn/C)))

(#|Strict -> |# struct ==>/⇓  ==> () #:transparent)
(#|Strict ->i|# struct ==>i/⇓ ==> () #:transparent)
(#|Blame|# Blm . ::= . (Blm [violator : ℓ]
                            [origin : -l]
                            [ctc : (Listof (U V P V^))]
                            [val : (Listof V^)]))
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
(define-syntax-rule (Blm/simp ℓ+ lo C V) (Blm (strip-ℓ ℓ) lo C V))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Simple helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Ctx-flip : (Ctx → Ctx)
  (match-lambda
    [(Ctx l+ l- lo ℓ) (Ctx l- l+ lo ℓ)]))
(define Ctx-with-ℓ : (Ctx ℓ → Ctx)
  (match-lambda**
    [((Ctx l+ l- lo _) ℓ) (Ctx l+ l- lo ℓ)]))

