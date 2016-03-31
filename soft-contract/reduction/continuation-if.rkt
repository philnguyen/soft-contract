#lang typed/racket/base

(provide ↝.if ↝.and)

(require racket/match
         "../utils/main.rkt"
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
        (define-values (Γ₁ Γ₂) (Γ+/-V M Γ* V s))
        
        (with-debugging/off
          ((δσ ΓWs ΓEs ℐs)
           (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ M σ* (-ℒ-with-Γ ℒ Γ₁)))
                  (with-Γ Γ₂ (⟦e₂⟧ M σ* (-ℒ-with-Γ ℒ Γ₂)))))
          (begin
            (printf "branching on ~a @ ~a:~n" (show-W¹ (-W¹ V s)) (show-Γ Γ*))
            (cond
              [Γ₁
               (define-values (φs₁ γs₁) (show-M-Γ M Γ₁))
               (printf "    - ~a~n" φs₁)
               (for ([γ γs₁])
                 (printf "       + ~a~n" γ))]
              [else
               (printf "    - #f~n")])
            (cond
              [Γ₂
               (define-values (φs₂ γs₂) (show-M-Γ M Γ₂))
               (printf "    - ~a~n" φs₂)
               (for ([γ γs₂])
                 (printf "       + ~a~n" γ))]
              [else
               (printf "    - #f~n")])
            (printf "Results:~n")
            (for ([A ΓWs])
              (printf "  - ~a~n" (show-A A)))
            (printf "Errors:~n")
            (for ([A ΓEs])
              (printf "  - ~a~n" (show-A A)))
            (printf "Pending:~n")
            (for ([ℐ ℐs])
              (printf "  - ~a~n" (show-ℐ ℐ)))
            (printf "~n"))))))
    (⟦e₀⟧ M σ ℒ)))

(: ↝.and : Mon-Party (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.and l ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['() ⟦e⟧]
    [(cons ⟦e⟧* ⟦e⟧s*) ((↝.if l ((↝.and l ⟦e⟧s*) ⟦e⟧*) ⟦ff⟧) ⟦e⟧)]))
