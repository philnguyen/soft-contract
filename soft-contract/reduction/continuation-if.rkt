#lang typed/racket/base

(provide ↝.if)

(require racket/match
         "../utils/function.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "helpers.rkt")

(: ↝.if : Mon-Party -⟦e⟧ -⟦e⟧ → -⟦ℰ⟧)
(define (((↝.if l ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ℒ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.if l ℰ ⟦e₁⟧ ⟦e₂⟧))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 (l Γ* Vs)
        (match-define (list V) Vs)
        (define-values (Γ₁ Γ₂) (Γ+/-V M σ* Γ* V s))
        #;(printf "branching on ~a with ~a and ~a~n"
                (show-W¹ (-W¹ V s))
                (and Γ₁ (show-Γ Γ₁))
                (and Γ₂ (show-Γ Γ₂)))
        (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ M σ* (-ℒ-with-Γ ℒ Γ₁)))
               (with-Γ Γ₂ (⟦e₂⟧ M σ* (-ℒ-with-Γ ℒ Γ₂)))))))
    (⟦e₀⟧ M σ ℒ)))
