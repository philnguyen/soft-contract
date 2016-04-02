#lang typed/racket/base

(provide ↝.begin ↝.begin0.v ↝.begin0.e)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../runtime/main.rkt"
         "helpers.rkt")

(: ↝.begin : (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.begin ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['() ⟦e⟧]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (define ⟦eᵣ⟧ ((↝.begin ⟦e⟧s*) ⟦e⟧*))
     (λ (M σ ℒ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin ℰ ⟦e⟧s))
         (λ (σ* Γ* _) (⟦eᵣ⟧ M σ* (-ℒ-with-Γ ℒ Γ*))))
        (⟦e⟧ M σ ℒ)))]))

(: ↝.begin0.v : (Listof -⟦e⟧) → -⟦ℰ⟧)
;; Waiting on `⟦e⟧` to be the returned value for `begin0`
(define ((↝.begin0.v ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['() ⟦e⟧]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (λ (M σ ℒ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin0.v ℰ ⟦e⟧s))
         (λ (σ* Γ* W)
           (define ⟦eᵣ⟧ ((↝.begin0.e W ⟦e⟧s*) ⟦e⟧*))
           (⟦eᵣ⟧ M σ* (-ℒ-with-Γ ℒ Γ*))))
        (⟦e⟧ M σ ℒ)))]))

(: ↝.begin0.e : -W (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.begin0.e W ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['()
     (λ (M σ ℒ)
       (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) W)} ∅ ∅))]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (define ⟦e⟧ᵣ ((↝.begin0.e W ⟦e⟧s*) ⟦e⟧*))
     (λ (M σ ℒ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin0.e W ℰ ⟦e⟧s))
         (λ (σ* Γ* _)
           (⟦e⟧ᵣ M σ* (-ℒ-with-Γ ℒ Γ*))))
        (⟦e⟧ M σ ℒ)))]))
