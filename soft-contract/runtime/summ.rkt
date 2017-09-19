#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit summ@
  (import pc^ pretty-print^)
  (export summ^)

  (define ⊥Ξ : -Ξ (hash))

  (: αₖ->ctx+pth : -αₖ → (Values -αₖ:ctx -αₖ:pth))
  (define αₖ->ctx+pth
    (match-lambda
      [(-ℬ $ ⟪ℋ⟫ xs e ρ Γ) (values (-ℬ:ctx ⟪ℋ⟫ xs e ρ) (-αₖ:pth $ Γ))]
      [(-ℳ $ ⟪ℋ⟫ ctx C V Γ) (values (-ℳ:ctx ⟪ℋ⟫ ctx C V) (-αₖ:pth $ Γ))]
      [(-ℱ $ ⟪ℋ⟫ l ℓ C V Γ) (values (-ℱ:ctx ⟪ℋ⟫ l ℓ C V) (-αₖ:pth $ Γ))]
      [(-ℋ𝒱 $ ⟪ℋ⟫) (values (-ℋ𝒱:ctx ⟪ℋ⟫) (-αₖ:pth $ ⊤Γ))]))

  (: ctx+pth->αₖ : -αₖ:ctx -αₖ:pth → -αₖ)
  (define (ctx+pth->αₖ ctx pth)
    (match-define (-αₖ:pth $ Γ) pth)
    (match ctx
      [(-ℬ:ctx ⟪ℋ⟫ xs e ρ) (-ℬ $ ⟪ℋ⟫ xs e ρ Γ)]
      [(-ℳ:ctx ⟪ℋ⟫ ctx C V) (-ℳ $ ⟪ℋ⟫ ctx C V Γ)]
      [(-ℱ:ctx ⟪ℋ⟫ l ℓ C V) (-ℱ $ ⟪ℋ⟫ l ℓ C V Γ)]
      [(-ℋ𝒱:ctx ⟪ℋ⟫) (-ℋ𝒱 $ ⟪ℋ⟫)])))
