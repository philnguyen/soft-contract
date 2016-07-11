#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "ap.rkt"
         racket/set
         racket/match)

(define-syntax-rule (with-error-handling (⟦k⟧ A Γ 𝒞 σ M) e ...)
  (λ (A Γ 𝒞 σ M)
    (cond [(-blm? A) (⟦k⟧ A Γ 𝒞 σ M)] ; TODO faster if had `αₖ` here
          [else e ...])))

;; Application
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

;; Conditional
(define/memo (if∷ [l : Mon-Party] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define-values (Γ₁ Γ₂) (Γ+/-V M Γ V s))
       (⊕ (with-Γ Γ₁ (⟦e⟧₁ ρ Γ₁ 𝒞 σ M ⟦k⟧))
          (with-Γ Γ₂ (⟦e⟧₂ ρ Γ₂ 𝒞 σ M ⟦k⟧)))]
      [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 σ M)])))

;; begin
(define/memo (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

;; begin0, waiting on first value
(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

;; begin0, already have first value
(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
       (⟦e⟧ ρ Γ 𝒞 σ M (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧)))]))

;; set!
(define/memo (set!∷ [α : -α] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define-values (ςs δσ δσₖ δM) (⟦k⟧ -Void/W Γ 𝒞 (σ⊔ σ α V #f) M))
       (values ςs (σ⊔ δσ α V #f) δσₖ δM)]
      [_
       (⟦k⟧ (-blm 'TODO 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 σ M)])))
