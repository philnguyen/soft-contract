#lang typed/racket/base

(provide fc@)

(require racket/sequence
         racket/match
         (except-in racket/set for/set for/seteq for*/set for*/seteq)
         syntax/parse/define
         typed/racket/unit
         bnf
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit fc@
  (import sto^ env^ val^ evl^
          prover^
          step^ compile^)
  (export fc^)

  (: fc : V^ V^ ℓ Φ^ Ξ:co Σ → (℘ Ξ))
  (define (fc C V ℓ Φ^ Ξ₀ Σ)
    (for/union : (℘ Ξ) ([Cᵢ (in-set C)])
      ((fc₁ Cᵢ) V ℓ Φ^ Ξ₀ Σ)))

  (⟦FC⟧ . ≜ . (V^ ℓ Φ^ Ξ:co Σ → (℘ Ξ)))

  (: fc₁ : V → ⟦FC⟧)
  (define fc₁
    (match-lambda
      [(And/C _ αℓ₁ αℓ₂) (fc-And/C αℓ₁ αℓ₂)]
      [(Or/C  _ αℓ₁ αℓ₂) (fc-Or/C αℓ₁ αℓ₂)]
      [(Not/C αℓ) (fc-Not/C αℓ)]
      [(One-Of/C bs) (fc-One-Of/C bs)]
      [(St/C _ 𝒾 αℓs) (fc-St/C 𝒾 αℓs)]
      [(X/C α) (fc-X/C α)]
      [(-b b) (fc-b b)]
      [V (fc-p V)]))

  (: fc-And/C : αℓ αℓ → ⟦FC⟧)
  (define ((fc-And/C αℓ₁ αℓ₂) Vₓ ℓ Φ^ Ξ Σ)
    (match-define (αℓ α₁ ℓ₁) αℓ₁)
    (fc (Σᵥ@ Σ α₁) Vₓ ℓ₁ Φ^ (K+ (F:Fc-And/C α₁ αℓ₂) Ξ) Σ))

  (: fc-Or/C : αℓ αℓ → ⟦FC⟧)
  (define ((fc-Or/C αℓ₁ αℓ₂) Vₓ ℓ Φ^ Ξ Σ)
    (match-define (αℓ α₁ ℓ₁) αℓ₁)
    (fc (Σᵥ@ Σ α₁) Vₓ ℓ₁ Φ^ (K+ (F:Fc-Or/C α₁ αℓ₂ Vₓ) Ξ) Σ))

  (: fc-Not/C : αℓ → ⟦FC⟧)
  (define ((fc-Not/C αℓ*) Vₓ ℓ Φ^ Ξ Σ)
    (match-define (αℓ α ℓ) αℓ*)
    (fc (Σᵥ@ Σ α) Vₓ ℓ Φ^ (K+ (F:Fc-Not/C Vₓ) Ξ) Σ))

  (: fc-One-Of/C : (Listof Base) → ⟦FC⟧)
  (define ((fc-One-Of/C bs) Vₓ ℓ Φ^ Ξ Σ)
    (define (er) (ret! (R '() Φ^) Ξ Σ))
    (define (ok [V : V^]) (ret! (R (list V) Φ^) Ξ Σ))
    (case (check-one-of Φ^ Vₓ bs)
      [(✓) {set (ok Vₓ)}]
      [(✗) {set (er)}]
      [else {set (ok (list->set (map -b bs))) (er)}]))

  (: fc-St/C : -𝒾 (Listof αℓ) → ⟦FC⟧)
  (define ((fc-St/C 𝒾 αℓs) Vₓ ℓ Φ^ Ξ Σ)
    (define (chk-fields [R^ : R^])
      (define-values (Vₓ* Φ^*) (collapse-R^-1 R^))
      (define ⟦chk⟧s : (Listof EΡ)
        (for/list ([αℓᵢ (in-list αℓs)] [i (in-naturals)] #:when (index? i))
          (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
          (define ⟦ref⟧ᵢ (mk-app ℓ (mk-V (-st-ac 𝒾 i)) (list (mk-V Vₓ*))))
          (EΡ (mk-fc ℓᵢ (mk-V (Σᵥ@ Σ αᵢ)) ⟦ref⟧ᵢ) ⊥Ρ)))
      (match ⟦chk⟧s
        [(cons (EΡ ⟦chk⟧ _) ⟦chk⟧s)
         {set (⟦chk⟧ ⊥Ρ Φ^* (K+ (F:Fc-Struct/C ℓ 𝒾 '() ⟦chk⟧s) Ξ) Σ)}]
        ['() {set (ret! (V->R (St 𝒾 '()) Φ^*) Ξ Σ)}]))
    (with-2-paths (λ () (split-results Σ (R (list Vₓ) Φ^) (-st-p 𝒾)))
      chk-fields
      (λ ([R^ : R^])
        (define Φ^ (collapse-R^/Φ^ R^))
        {set (ret! (R '() Φ^) Ξ Σ)})))

  (: fc-X/C : α → ⟦FC⟧)
  (define ((fc-X/C α) Vₓ ℓ Φ^ Ξ Σ)
    (fc (Σᵥ@ Σ α) Vₓ ℓ Φ^ Ξ Σ))

  (: fc-b : Base → ⟦FC⟧)
  (define ((fc-b b) Vₓ ℓ Φ^ Ξ Σ)
    (define ⟦b⟧ (mk-V (-b b)))
    (define ⟦ap⟧ (mk-app ℓ (mk-V 'equal?) (list (mk-V Vₓ) ⟦b⟧)))
    {set (⟦ap⟧ ⊥Ρ Φ^ (K+ (F:If (ℓ-src ℓ) ⟦b⟧ (mk-W '()) ⊥Ρ) Ξ) Σ)})

  (: fc-p : V → ⟦FC⟧)
  (define ((fc-p P) Vₓ ℓ Φ^ Ξ Σ)
    (define ⟦ap⟧ (mk-app ℓ (mk-V P) (list (mk-V Vₓ))))
    {set (⟦ap⟧ ⊥Ρ Φ^ (K+ (F:If (ℓ-src ℓ) (mk-V Vₓ) (mk-W '()) ⊥Ρ) Ξ) Σ)})
  )
