#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-signature local-prover-core^
  ([check : (Σ Φ V (Listof V) → ?Dec)]
   [check-one-of : (V (Listof Base) → ?Dec)]
   [∧  : (R V → R)]
   [∧¬ : (R V → R)]
   [V-arity : (case-> [Clo → (U Natural arity-at-least)]
                      [Case-Clo → Arity]
                      [V → (Option Arity)])]))

(define-signature ext-prover-core^
  ([check : (Σ Φ V (Listof V) → ?Dec)]))

(define-signature sat-result^
  ([⊔ : (?Dec ?Dec * → ?Dec)]
   [⊔* : (∀ (X) (X → ?Dec) (Listof X) → ?Dec)]
   [⊔*/set : (∀ (X) (X → ?Dec) (Setof X) → ?Dec)]
   [neg : (?Dec → ?Dec)]
   [bool->Dec : (Boolean → Dec)]))
