#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../runtime/signatures.rkt")

(define-signature local-prover-core^
  ([check : (Σ Φ V (Listof V) → ?Dec)]
   [∧  : (Φ^ V W → Φ^)]
   [∧¬ : (Φ^ V W → Φ^)]))

(define-signature ext-prover-core^
  ([check : (Σ Φ V (Listof V) → ?Dec)]))

(define-signature sat-result^
  ([⊔ : (?Dec ?Dec * → ?Dec)]
   [⊔* : (∀ (X) (X → ?Dec) (Listof X) → ?Dec)]
   [⊔*/set : (∀ (X) (X → ?Dec) (Setof X) → ?Dec)]
   [neg : (?Dec → ?Dec)]
   [bool->Dec : (Boolean → Dec)]))
