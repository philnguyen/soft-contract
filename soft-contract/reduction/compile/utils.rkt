#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         syntax/parse/define
         "../../utils/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(define-simple-macro (with-error-handling (⟦k⟧:id A:id Γ:id 𝒞:id Σ:id) e ...)
  (λ (A Γ 𝒞 Σ)
    (cond [(-blm? A) (⟦k⟧ A Γ 𝒞 Σ)] ; TODO faster if had `αₖ` here
          [else e ...])))

(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))
