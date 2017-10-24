#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/bool
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "signatures.rkt")

(define-unit path@
  (import pretty-print^ val^)
  (export path^)

  (define φ₀ : -φ (-φ (hash) (hasheq)))

  (: φ⊔ : -φ ⟪α⟫ (U -V -V^) → -φ)
  (define (φ⊔ φ α V)
    (define V^ (if (set? V) V {set V}))
    (match-define (-φ Γ δσ) φ)
    (error 'TODO))

  (: φ⊔* : -φ (Listof ⟪α⟫) (Listof (U -V -V^)) → -φ)
  (define (φ⊔* φ αs Vs)
    (for/fold ([φ : -φ φ]) ([α : ⟪α⟫ αs] [V Vs])
      (φ⊔ φ α V)))

  (: φ+ : -φ -t → -φ)
  (define (φ+ φ t)
    (match-define (-φ Γ δσ) φ)
    (define Γ*
      (match t
        [(-t.@ p (and xs (list _)))
         (hash-update Γ xs (refine-with p) mk-∅)]
        [_
         (hash-update Γ (list t) (refine-with 'values) mk-∅)]))
    (-φ Γ* δσ))

  (: φ-with-condition : -φ -Γ → -φ)
  (define (φ-with-condition φ Γ)
    (match-define (-φ _ δσ) φ)
    (-φ Γ δσ))

  (: bind-args : -ρ -H -φ (Listof Symbol) (Listof -V^) → (Values -ρ -φ))
  (define (bind-args ρ H φ xs Vs)
    (for/fold ([ρ : -ρ ρ] [φ : -φ φ])
              ([x xs] [V Vs])
      (define α (-α->⟪α⟫ (-α.x x H)))
      (values (hash-set ρ x α) (φ⊔ φ α V))))

  (: refine-with : -h → (℘ -h) → (℘ -h))
  (define ((refine-with h) hs) (set-add hs h))
  )
