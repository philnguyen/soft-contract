#lang typed/racket/base

(provide debug@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         racket/list
         typed/racket/unit
         set-extras
         typed-racket-hacks
         unreachable
         bnf
         traces/typed
         intern
         set-extras
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "reduction/signatures.rkt"
         "signatures.rkt"
         )

(define-interner Iᵥ Σᵥ)
(define-interner Iₖ Σₖ)
(define-interner Iₐ Σₐ)

(define-unit debug@
  (import step^)
  (export debug^)

  (: viz : (U -prog ⟦E⟧) → Σ)
  (define (viz p)
    ;; Compacting each store to its version to display
    (Ξ* . ≜ . (List Ξ Iᵥ Iₖ Iₐ))
    
    (define-values (Ξ₀ Σ₀) (inj p))

    (define (Ξ->Ξ* [Ξ : Ξ]) : Ξ*
      ;; depending on mutable state Σ₀
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (list Ξ (Iᵥ-of Σᵥ) (Iₖ-of Σₖ) (Iₐ-of Σₐ)))

    (define Ξ*->Ξ : (Ξ* → Ξ)
      (match-lambda [(list Ξ _ _ _) Ξ]))
    
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (λ (Ξ*) (map/set Ξ->Ξ* (↝ (Ξ*->Ξ Ξ*) Σ₀))))
    
    (function-traces ↝₁ (Ξ->Ξ* Ξ₀))
    Σ₀)
  )
