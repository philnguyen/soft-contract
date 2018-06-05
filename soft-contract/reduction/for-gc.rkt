#lang typed/racket/base

(provide for-gc@)

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt")

(define-unit for-gc@
  (import)
  (export for-gc^)

  (: V-root : V → (℘ α))
  (define V-root
    (match-lambda
      [(St _ αs) (list->seteq αs)]
      [(Vect αs) (list->seteq αs)]
      [(Vect^ α V) (set-add (set-union-map V-root V ∅eq) α)]
      [(Hash^ αₖ αᵥ _) {seteq αₖ αᵥ}]
      [(Set^ α _) {seteq α}]
      [(Clo _ _ Ρ) (Ρ-root Ρ)]
      [(Case-Clo clos) (apply ∪ ∅eq (map (compose Ρ-root Clo-_2) clos))]
      [(X/G _ C α) {set-add (V-root C) α}]
      [(Sealed α) ∅eq #;{seteq α}] ; TODO confirm ok
      [(And/C _ (αℓ α₁ _) (αℓ α₂ _)) {seteq α₁ α₂}]
      [(Or/C _ (αℓ α₁ _) (αℓ α₂ _)) {seteq α₁ α₂}]
      [(Not/C (αℓ α _)) {seteq α}]
      [(X/C α) {seteq α}]
      [(==> (-var αℓs ?αℓ) ?αℓs)
       (∪ (list->seteq (map αℓ-_0 αℓs))
          (if ?αℓ {seteq (αℓ-_0 ?αℓ)} ∅eq)
          (if ?αℓs (list->seteq (map αℓ-_0 ?αℓs)) ∅eq))]
      [(==>i Doms Rng) (apply ∪ (Dom-root Rng) (map Dom-root Doms))]
      [(∀/C _ _ Ρ) (Ρ-root Ρ)]
      [(Case-=> Cs) (apply ∪ ∅eq (map V-root Cs))]
      [(St/C _ _ αℓs) (list->seteq (map αℓ-_0 αℓs))]
      [(Vectof (αℓ α _)) {seteq α}]
      [(Vect/C αℓs) (list->seteq (map αℓ-_0 αℓs))]
      [(Hash/C (αℓ αₖ _) (αℓ αᵥ _)) {seteq αₖ αᵥ}]
      [(Set/C (αℓ α _)) {seteq α}]
      [(Seal/C x H l) {seteq (mk-α (-α:sealed x H))}]
      [_ ∅eq]))

  (: Ρ-root : Ρ → (℘ α))
  (define (Ρ-root Ρ) (list->seteq (hash-values Ρ)))

  (: Dom-root : Dom → (℘ α))
  (define (Dom-root D)
    (define C (Dom-ctc D))
    (if (Clo? C) (Ρ-root (Clo-_2 C)) {seteq C}))
  
  )
