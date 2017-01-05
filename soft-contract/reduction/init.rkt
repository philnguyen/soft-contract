#lang typed/racket/base

(provide 𝑰 havoc*)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         (only-in "../proof-relation/base-assumptions.rkt" V-arity)
         "../externals/main.rkt" ; for side-effects
         "compile/utils.rkt"
         "compile/app.rkt"
         "havoc.rkt")

(: 𝑰 : (Listof -module) → (Values -σ -e))
;; Load the initial store and havoc-ing expression for given module list
(define (𝑰 ms)
  (define e† (gen-havoc-exp ms))
  (define hv (gen-havoc-clo ms))
  (define σ (⊥σ))
  (σ⊕*! σ [(-α->-⟪α⟫ havoc-𝒾) ↦ hv]
          [(-α->-⟪α⟫ (-α.wrp havoc-𝒾)) ↦ hv])
  ;(ensure-singletons σ) ; disable this in production
  (values σ e†))
