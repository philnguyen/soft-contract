#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../runtime/signatures.rkt")

(define-signature local-prover-core^
  ([check : (Σ Φ V (Listof V) → Valid)]))

(define-signature ext-prover-core^
  ([check : (Σ Φ V (Listof V) → Valid)]))

(define-signature sat-result^
  ([⊔ : (Valid Valid * → Valid)]
   [⊔* : (∀ (X) (X → Valid) (Setof X) → Valid)]
   [neg : (Valid → Valid)]
   [bool->sat : (Boolean → (U '✓ '✗))]))
