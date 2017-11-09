#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/list
         racket/match
         racket/bool
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit path@
  (import pretty-print^ env^ val^ widening^)
  (export path^)

  (define φ₀ : -φ (-φ (hash) (hasheq)))

  (: φ⊔ : -φ ⟪α⟫ (U -V -V^) → -φ)
  (define (φ⊔ φ α V)
    (define V^ (if (set? V) V {set V}))
    (match-define (-φ Γ δσ) φ)
    (define δσ* (hash-update δσ α (λ ([V^₀ : -V^]) (V⊕ V^₀ V^)) mk-∅))
    (-φ Γ δσ*))

  (: φ⊔* : -φ (Listof ⟪α⟫) (Listof (U -V -V^)) → -φ)
  (define (φ⊔* φ αs Vs)
    (for/fold ([φ : -φ φ]) ([α : ⟪α⟫ αs] [V Vs])
      (φ⊔ φ α V)))

  (: φ-with-condition : -φ -Γ → -φ)
  (define (φ-with-condition φ Γ)
    (match-define (-φ _ δσ) φ)
    (-φ Γ δσ))

  (: bind-args : -ρ ℓ -H -φ -formals (Listof -V^) → (Values -ρ -φ))
  (define (bind-args ρ ℓ H φ fml Vs)

    (: bind-init : -ρ -φ (Listof Symbol) (Listof -V^) → (Values -ρ -φ))
    (define (bind-init ρ φ xs Vs)
      (for/fold ([ρ : -ρ ρ] [φ : -φ φ])
                ([x (in-list xs)] [V (in-list Vs)])
        (define α (-α->⟪α⟫ (-α.x x H)))
        (values (hash-set ρ x α) (φ⊔ φ α V))))
    
    (match fml
      [(? list? xs) (bind-init ρ φ xs Vs)]
      [(-var xs xᵣ)
       (define-values (Vs-init Vs-rest) (split-at Vs (length xs)))
       (define-values (ρ₁ φ₁) (bind-init ρ φ xs Vs-init))
       (define-values (Vᵣ φ₂) (alloc-rest-args ℓ H φ₁ Vs-rest))
       (define αᵣ (-α->⟪α⟫ (-α.x xᵣ H)))
       (values (ρ+ ρ₁ xᵣ αᵣ) (φ⊔ φ₂ αᵣ Vᵣ))]))

  (: alloc-rest-args : ([ℓ -H -φ (Listof -V^)] [#:end -V] . ->* . (Values -V -φ)))
  (define (alloc-rest-args ℓ H φ V^s #:end [tail -null])
    (let go ([V^s : (Listof -V^) V^s] [φ : -φ φ] [i : Natural 0])
      (match V^s
        ['() (values tail φ)]
        [(cons V^ V^s*)
         (define αₕ (-α->⟪α⟫ (-α.var-car ℓ H i)))
         (define αₜ (-α->⟪α⟫ (-α.var-cdr ℓ H i)))
         (define-values (Vₜ φₜ) (go V^s* φ (+ 1 i)))
         (define φ* (φ⊔ (φ⊔ φₜ αₕ V^) αₜ Vₜ))
         (values (-Cons αₕ αₜ) φ*)])))

  (: t-names : -t → (℘ Integer))
  (define t-names
    (match-lambda
      [(? integer? i) {seteq i}]
      [(? -b?) ∅eq]
      [(-t.@ _ ts) (apply ∪ ∅eq (map t-names ts))]))
  )
