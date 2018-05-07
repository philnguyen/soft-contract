#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         set-extras
         bnf
         "ast/signatures.rkt"
         "runtime/signatures.rkt")

(Runnable . ::= . -prog -e [#:reuse (Listof Path-String)])

(define-signature verifier^
  ([run : (Runnable → (Values (℘ Blm) Σ))]
   [havoc : ((Listof Path-String) → (Values (℘ Blm) Σ))]
   [havoc-last : ((Listof Path-String) → (Values (℘ Blm) Σ))]
   [havoc/profile
    : ([(Listof Path-String)] [#:delay Positive-Real] . ->* . (Values (℘ Blm) Σ))]
   [viz : (Runnable → Σ)]
   [viz-call-graph : (Runnable → Void)]))

(define-signature parser^ ; TODO
  ([parse-files : ((Listof Path-String) → (Listof -module))]
   [parse-module : (Syntax → -module)]
   [parse-expr : (Syntax → -e)]
   [canonicalize-path : (Path-String → Path-String)]))

(define-signature prims^ ; TODO
  ([get-prim : (Symbol → ⟦F⟧^)]
   [o⊢o : (Symbol Symbol → ?Dec)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [prim-arity : (Symbol → Arity)]
   [parse-prim : (Identifier → (Option -prim))]
   [implement-predicate : (Σ Φ^ -o W → R^)]
   [vec-len : (T^ → T^)]))

(define-signature prover^
  ([split-results : ([Σ (U R R^)] [T #:fast? Boolean] . ->* . (Values R^ R^))]
   [partition-results : ([Σ (U R R^)] [T #:fast? Boolean] . ->* . (Values R^ R^ R^))]
   [check-plausible-index : ([Σ (U R R^) Natural] [#:fast? Boolean] . ->* . (Values R^ R^))]
   [check-one-of : (Φ^ T^ (Listof Base) → ?Dec)]
   [T-arity : (case-> [Clo → (U Natural arity-at-least)]
                      [Case-Clo → Arity]
                      [T → (Option Arity)])]
   [T->V : ((U Σ Σᵥ) Φ^ (U T T^) → V^)]
   [⊔T! : (Σ Φ^ α (U T T^) → Void)]
   [⊔T*! : (Σ Φ^ (Listof α) (Listof T^) → Void)]
   #|
   [p⇒p : (-h -h → -R)]
   [V+ : (-σ -φ -V^ (U -h -V) → -V^)]
   [V- : (-σ -φ -V^ (U -h -V) → -V^)]
   [φ+pV : (-φ -h (Listof -V) → -φ)]
   [plausible-index? : (-σ -φ -V^ Natural → Boolean)]
   [sat-one-of : (-V^ (℘ Base) → -R)]
   [V-arity : (case->
   [-Clo → Arity]
   [-Case-Clo → Arity]
   [-V → (Option Arity)])]
   |#))

