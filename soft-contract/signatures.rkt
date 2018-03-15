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
   [viz : (Runnable → Σ)]))

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

(define-signature proof-system^
  ([plausible-splits : (Σ R^ → (Values Φ^ Φ^))]
   [plausible-sats : (Σ Φ^ P W → (Values Φ^ Φ^))]
   #|
   [p⇒p : (-h -h → -R)]
   [V∈C : (-σ -φ -V^ (U -h -V) → -R)]
   [φ+/-pV^ : (-σ -φ -h -V^ * → (Values (℘ -φ) (℘ -φ)))]
   [p∋V^ : (-σ -φ -h -V^ * → -R)]
   [quick-p∋V^ : (-σ -φ -h -V^ * → -R)]
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

