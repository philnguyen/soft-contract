#lang typed/racket/base

(provide alloc@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function const)
         racket/set
         racket/list
         racket/match
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit alloc@
  (import static-info^)
  (export alloc^)

  (: mutable? : α → Boolean)
  (define (mutable? α)
    (match (inspect-α α)
      [(-α:x x _) (assignable? x)]
      [(-α:fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α:idx?) #t]
      [_ #f]))

  (: bind-args! : Σ Ρ ℓ H Φ^ -formals W → Ρ)
  (define (bind-args! Σ Ρ₀ ℓ H Φ^ xs Vs)
    ???)

  (: ⊔ᵥ! : Σ α (U V V^) → Void)
  (define (⊔ᵥ! Σ α V) ???)

  (: ⊔ᵥ*! : Σ (Listof α) (Listof V^) → Void)
  (define (⊔ᵥ*! Σ αs Vs)
    (for ([α (in-list αs)] [V (in-list Vs)])
      (⊔ᵥ! Σ α V)))

  (: ⊔ₐ! : Σ K (U R R^) → Void)
  (define (⊔ₐ! Σ K R) ???)
  
  (: ⊔ₖ! : Σ αₖ Rt → Void)
  (define (⊔ₖ! Σ αₖ K) ???)

  )

