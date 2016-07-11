#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         racket/set
         racket/match)

(define-syntax-rule (with-error-handling (⟦k⟧ A Γ 𝒞 σ M) e ...)
  (λ (A Γ 𝒞 σ M)
    (cond [(-blm? A) (⟦k⟧ A Γ 𝒞 σ M)] ; TODO faster if had `αₖ` here
          [else e ...])))

(define/memo (ap∷ [Ws : (Listof -W¹)]
                  [⟦e⟧s : (Listof -⟦e⟧)]
                  [ρ : -ρ]
                  [l : Mon-Party]
                  [ℓ : -ℓ]
                  [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define Ws* (cons (-W¹ V s) Ws))
       (match ⟦e⟧s
         ['()
          (match-define (cons Wₕ Wₓs) (reverse Ws*))
          (error "TODO")]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (⟦e⟧ ρ Γ 𝒞 σ M (ap∷ Ws* ⟦e⟧s* ρ l ℓ ⟦k⟧))])]
      [_
       (⟦k⟧ (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 σ M)])))

(define/memo (if∷ [l : Mon-Party] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (error "TODO")]
      [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 σ M)])))

(define/memo (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))


(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧)))]))

#|
(: ap : -Γ -𝒞 -σ -M Mon-Party -ℓ -W¹ (Listof -W¹) → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
(define (ap Γ 𝒞 σ M l ℓ Wₕ Wₓs)
  (error "TODO"))
|#
