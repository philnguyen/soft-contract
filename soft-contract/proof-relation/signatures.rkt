#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-signature local-prover-core^
  ([check : ((U Σ Σᵥ) Φ T (Listof T) → ?Dec)]
   [check-one-of : (T (Listof Base) → ?Dec)]
   [∧  : (R T → R)]
   [∧¬ : (R T → R)]
   [T-arity : (case-> [Clo → (U Natural arity-at-least)]
                      [Case-Clo → Arity]
                      [T → (Option Arity)])]
   [T->V : ((U Σ Σᵥ) Φ^ (U T T^) → V^)]
   [V^+ : (case-> [Σ V^ V → V^]
                  [Σ T^ V → T^])]
   [Ψ+ : (case-> [Ψ (U P (℘ P)) (Listof S) → Ψ]
                 [Φ (U P (℘ P)) (Listof S) → Φ]
                 [Φ^ (U P (℘ P)) (Listof S) → Φ^])]
   [Ps⊢P : ((℘ P) P → ?Dec)]
   [Ps+ : ((℘ P) P → (℘ P))]))

(define-signature ext-prover-core^
  ([check : ((U Σ Σᵥ) Φ T (Listof T) → ?Dec)]))

(define-signature sat-result^
  ([⊔ : (?Dec ?Dec * → ?Dec)]
   [⊔* : (∀ (X) (X → ?Dec) (Listof X) → ?Dec)]
   [⊔*/set : (∀ (X) (X → ?Dec) (Setof X) → ?Dec)]
   [neg : (?Dec → ?Dec)]
   [bool->Dec : (Boolean → Dec)]))
