#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt")

(define-signature local-prover-base^
  ([add-implication! : (Symbol Symbol → Void)]
   [add-exclusion! : (Symbol Symbol → Void)]
   [get-weakers : (Symbol → (℘ Symbol))]
   [get-strongers : (Symbol → (℘ Symbol))]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [o⇒o : (Symbol Symbol → -R)]
   [set-range! : (Symbol Symbol → Void)]
   [get-conservative-range : (Symbol → Symbol)]
   [set-partial! : (Symbol Natural → Void)]
   [partial-prims : (HashTable Symbol Natural)]
   [V-arity : (-V → (Option Arity))]))

(define-signature local-prover^
  ([Γ⊢t : ((℘ -t) -?t → -R)]
   [⊢V : (-V → -R)]
   [p∋Vs : (-σ (U -h -v -V) -V * → -R)]
   [p⇒p : (-h -h → -R)]
   [ps⇒p : ((℘ -h) -h → -R)]
   [plausible-V-t? : ((℘ -t) -V -?t → Boolean)]
   [sat-one-of : (-V (Listof Base) → -R)]))

(define-signature external-prover^
  ([ext-prove : (-M -Γ -t → -R)]))
