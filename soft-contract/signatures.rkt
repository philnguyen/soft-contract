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
   [o⇒o : (Symbol Symbol → Valid)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [prim-arity : (Symbol → Arity)]
   [parse-prim : (Identifier → (Option -prim))]
   [implement-predicate : (Σ Φ^ -o W → R^)]))

(define-signature prover^
  ([plausible-splits : (case-> [Σ R^ → (Values Φ^ Φ^)]
                               [Σ R^ Boolean → (Values Φ^ Φ^)]
                               [Σ Φ^ V W → (Values Φ^ Φ^)]
                               [Σ Φ^ V W Boolean → (Values Φ^ Φ^)])]
   [partition-sats : ([Σ Φ^ V W] [#:fast? Boolean] . ->* . (Values Φ^ Φ^ Φ^))]
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

