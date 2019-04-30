#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         set-extras
         bnf
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         #;"primitives/signatures.rkt")

(Runnable . ::= . -prog -e [#:reuse (Listof Path-String)])

(define-signature verifier^
  ([run : (Runnable → (Values (℘ Err) $))]
   [havoc : ((Listof Path-String) → (Values (℘ Err) $))]
   [optimize : (-module (℘ Err) → -module)]
   [havoc-last : ((Listof Path-String) → (Values (℘ Err) $))]
   [havoc/profile
    : ([(Listof Path-String)] [#:delay Positive-Real] . ->* . (Values (℘ Err) $))]
   [verify-modules : ((Listof Syntax) → (℘ Err))]
   #;[viz : (Runnable → Σ)]))

(define-signature parser^ ; TODO
  ([parse-files : ((Listof Path-String) → (Listof -module))]
   [parse-stxs : ((Listof Syntax) → (Listof -module))]
   [parse-module : (Syntax → -module)]
   [parse-expr : (Syntax → -e)]
   [canonicalize-path : (Path-String → Path-String)]))

(define-signature prims^ ; TODO
  ([get-prim : (Symbol → Σ ℓ W → (Values R (℘ Err)))]
   [implement-predicate : (Σ -o W → (Values R (℘ Err)))]
   [prim-arity : (Symbol → Arity)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [o⊢o : (Symbol Symbol → ?Dec)]
   [parse-prim : (Identifier → (Option -prim))]
   )) 
