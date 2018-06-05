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
  (import meta-functions^
          sto^ env^ val^ evl^
          prover^
          step^ compile^ approx^ alloc^)
  (export fc^)

  (: fc : T^ T^ ℓ Φ^ Ξ:co Σ → (℘ Ξ))
  (define (fc C V ℓ Φ^ Ξ₀ Σ)
    (for/union : (℘ Ξ) ([Cᵢ (in-set (T->V Σ Φ^ C))])
      ((fc₁ Cᵢ) V ℓ Φ^ Ξ₀ Σ)))

  (⟦FC⟧ . ≜ . (T^ ℓ Φ^ Ξ:co Σ → (℘ Ξ)))

  (: fc₁ : V → ⟦FC⟧)
  (define fc₁
    (match-lambda
      [(And/C _ αℓ₁ αℓ₂) (fc-And/C αℓ₁ αℓ₂)]
      [(Or/C  _ αℓ₁ αℓ₂) (fc-Or/C αℓ₁ αℓ₂)]
      [(Not/C αℓ) (fc-Not/C αℓ)]
      [(One-Of/C bs) (fc-One-Of/C bs)]
      [(St/C _ 𝒾 αℓs) (fc-St/C 𝒾 αℓs)]
      [(? X/C? C) (fc-X/C C)]
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
    (define (ok [V : T^]) (ret! (R (list V) Φ^) Ξ Σ))
    (case (check-one-of Φ^ Vₓ bs)
      [(✓) {set (ok Vₓ)}]
      [(✗) {set (er)}]
      [else {set (ok (list->set (map -b bs))) (er)}]))

  (: fc-St/C : -𝒾 (Listof αℓ) → ⟦FC⟧)
  (define ((fc-St/C 𝒾 αℓs) Vₓ ℓ Φ^ Ξ Σ)
    (define (chk-fields [R^ : R^])
      (define-values (Vₓ* Φ^*) (collapse-R^-1 Σ R^))
      (define ⟦chk⟧s : (Listof EΡ)
        (for/list ([αℓᵢ (in-list αℓs)] [i (in-naturals)] #:when (index? i))
          (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
          (define ⟦ref⟧ᵢ (mk-app ℓ (mk-T (-st-ac 𝒾 i)) (list (mk-T Vₓ*))))
          (EΡ (mk-fc ℓᵢ (mk-T (Σᵥ@ Σ αᵢ)) ⟦ref⟧ᵢ) ⊥Ρ)))
      (match ⟦chk⟧s
        [(cons (EΡ ⟦chk⟧ _) ⟦chk⟧s)
         {set (⟦chk⟧ ⊥Ρ Φ^* (K+ (F:Fc-Struct/C ℓ 𝒾 '() ⟦chk⟧s) Ξ) Σ)}]
        ['() {set (ret! (T->R (St 𝒾 '()) Φ^*) Ξ Σ)}]))
    (with-2-paths (λ () (split-results Σ (R (list Vₓ) Φ^) (-st-p 𝒾)))
      chk-fields
      (λ ([R^ : R^])
        (define Φ^ (collapse-R^/Φ^ R^))
        {set (ret! (R '() Φ^) Ξ Σ)})))

  (: fc-X/C : X/C → ⟦FC⟧)
  (define ((fc-X/C C) Vₓ ℓ Φ^ Ξ Σ)
    (match-define (Ξ:co (K _ (αₖ H _ _)) ?m) Ξ)
    (match-define (X/C α) C)
    (define H* (H+ H ℓ C))
    (⊔ₖ! Σ α* (Rt Φ^ {seteq α} Ξ))
    (define x (X/C->binder C))
    (define-values (Φ^* Ρ) (bind-args! Φ^ ⊥Ρ (-var (list x) #f) (list Vₓ) H* Σ))
    (define α* (αₖ H* Φ^* (βₖ:fc ℓ α)))
    (define Ξ* (Ξ:co (K (list (F:Fc:C ℓ (Σᵥ@ Σ α))) α*) ?m))
    {set (ret! (R (list (S:α (hash-ref Ρ x))) Φ^*) Ξ* Σ)})

  (: fc-b : Base → ⟦FC⟧)
  (define ((fc-b b) Vₓ ℓ Φ^ Ξ Σ)
    (define ⟦b⟧ (mk-T (-b b)))
    (define ⟦ap⟧ (mk-app ℓ (mk-T 'equal?) (list (mk-T Vₓ) ⟦b⟧)))
    {set (⟦ap⟧ ⊥Ρ Φ^ (K+ (F:If (ℓ-src ℓ) ⟦b⟧ (mk-W '()) ⊥Ρ) Ξ) Σ)})

  (: fc-p : V → ⟦FC⟧)
  (define ((fc-p P) Vₓ ℓ Φ^ Ξ Σ)
    (define ⟦ap⟧ (mk-app ℓ (mk-T P) (list (mk-T Vₓ))))
    {set (⟦ap⟧ ⊥Ρ Φ^ (K+ (F:If (ℓ-src ℓ) (mk-T Vₓ) (mk-W '()) ⊥Ρ) Ξ) Σ)})
  )
