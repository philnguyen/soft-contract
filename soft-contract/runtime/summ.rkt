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
      [(-B $ H xs e ρ Γ) (values (-B:ctx H xs e ρ) (-αₖ:pth $ Γ))]
      [(-M $ H ctx C V Γ) (values (-M:ctx H ctx C V) (-αₖ:pth $ Γ))]
      [(-F $ H l ℓ C V Γ) (values (-F:ctx H l ℓ C V) (-αₖ:pth $ Γ))]
      [(-HV $ t) (values (-HV:ctx t) (-αₖ:pth $ ⊤Γ))]))

  (: ctx+pth->αₖ : -αₖ:ctx -αₖ:pth → -αₖ)
  (define (ctx+pth->αₖ ctx pth)
    (match-define (-αₖ:pth $ Γ) pth)
    (match ctx
      [(-B:ctx H xs e ρ) (-B $ H xs e ρ Γ)]
      [(-M:ctx H ctx C V) (-M $ H ctx C V Γ)]
      [(-F:ctx H l ℓ C V) (-F $ H l ℓ C V Γ)]
      [(-HV:ctx t) (-HV $ t)])))
