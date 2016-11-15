#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/set
         syntax/parse/define
         "../../utils/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(define-syntax compute-frame-roots
  (syntax-parser
    [(_) #'∅]
    [(_ root:id) #'(->αs root)]
    [(_ root:id ...) #'(∪ (->αs root) ...)]))

(define-simple-macro (with-error-handling (⟦k⟧:id A:id $:id Γ:id 𝒞:id Σ:id)
                       #:roots (root:id ...)
                       e ...)
  (let ([αₖ (⟦k⟧->αₖ ⟦k⟧)]
        [frame-roots (compute-frame-roots root ...)]
        [tail-roots (⟦k⟧->roots ⟦k⟧)])
    (define ⟦k⟧* : -⟦k⟧!
      (λ (A $ Γ 𝒞 Σ)
        (cond [(-blm? A)
               (case (-blm-violator A)
                 [(havoc Λ †) ∅]
                 [else ; FIXME duplicate code from `rt`
                  (define M (-Σ-M Σ))
                  (vm⊔! M αₖ (-ΓA Γ A))
                  {set (-ς↓ αₖ Γ A)}])]
              [else e ...])))
    (set-⟦k⟧->αₖ! ⟦k⟧* αₖ)
    (add-⟦k⟧-roots! ⟦k⟧* (∪ frame-roots tail-roots))
    ⟦k⟧*))

(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))
