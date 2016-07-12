#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "app.rkt"
         racket/set
         racket/match)

(define-syntax-rule (with-error-handling (⟦k⟧ A Γ 𝒞 σ M) e ...)
  (λ (A Γ 𝒞 σ M)
    (cond [(-blm? A) (⟦k⟧ A Γ 𝒞 σ M)] ; TODO faster if had `αₖ` here
          [else e ...])))

;; Base continuation that returns locally finished configuration
(define/memo (rt [αₖ : -αₖ]) : -⟦k⟧
  (λ (A Γ 𝒞 σ M)
    (values {set (-ς↓ αₖ Γ A)} ⊥σ ⊥σₖ (hash αₖ {set (-ΓA Γ A)}))))

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
          (app l ℓ Wₕ Wₓs Γ 𝒞 σ M ⟦k⟧)]
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

;; let-values
(define/memo (let∷ [l : Mon-Party]
                   [xs : (Listof Var-Name)]
                   [⟦bnd⟧s : (Listof (Pairof (Listof Var-Name) -⟦e⟧))]
                   [bnd-Ws : (Listof (List Var-Name -V -s))]
                   [⟦e⟧ : -⟦e⟧]
                   [ρ : -ρ]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (define n (length xs))
    (cond
      [(= n (length Vs))
       (define bnd-Ws*
         (for/fold ([acc : (Listof (List Var-Name -V -s)) bnd-Ws])
                   ([x xs] [V Vs] [sₓ (split-values s n)])
           (cons (list x V sₓ) acc)))
       (match ⟦bnd⟧s
         ['()
          (define-values (ρ* σ* δσ Γ*)
            (for/fold ([ρ : -ρ ρ] [σ : -σ σ] [δσ : -Δσ ⊥σ] [Γ : -Γ Γ])
                      ([bnd-W bnd-Ws])
              (match-define (list (? Var-Name? x) (? -V? Vₓ) (? -s? sₓ)) bnd-W)
              (define α (-α.x x 𝒞))
              (values (ρ+ ρ x α)
                      (σ⊔ σ  α Vₓ #t)
                      (σ⊔ δσ α Vₓ #t)
                      (-Γ-with-aliases Γ x sₓ))))
          (define-values (ςs δσ₀ δσₖ δM) (⟦e⟧ ρ* Γ* 𝒞 σ* M ⟦k⟧))
          (values ςs (⊔σ δσ₀ δσ) δσₖ δM)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ Γ 𝒞 σ M (let∷ l xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'let-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 σ M)])))

;; letrec-values
(define/memo (letrec∷ [l : Mon-Party]
                      [xs : (Listof Var-Name)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Var-Name) -⟦e⟧))]
                      [⟦e⟧ : -⟦e⟧]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W Vs s) A)
    (define n (length xs))
    (cond
      [(= n (length Vs))
       (define-values (σ* δσ Γ*)
         (for/fold ([σ  : -σ  σ]
                    [δσ : -Δσ ⊥σ]
                    [Γ  : -Γ  Γ])
                   ([x xs] [Vₓ Vs] [sₓ (split-values s n)])
           (define α (-α.x x 𝒞))
           (values (σ⊔ σ  α Vₓ #t)
                   (σ⊔ δσ α Vₓ #t)
                   (Γ+ (-Γ-with-aliases Γ x sₓ) (-?@ 'defined? (-x x))))))
       (define-values (ςs δσ₀ δσₖ δM)
         (match ⟦bnd⟧s
           ['()
            (⟦e⟧ ρ Γ* 𝒞 σ* M ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ Γ* 𝒞 σ* M (letrec∷ l xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))]))
       (values ςs (⊔σ δσ₀ δσ) δσₖ δM)]
      [else
       (define blm
         (-blm l 'letrec-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 σ M)])))

;; μ/c
(define/memo (μ/c∷ [l : Mon-Party]
                   [x : -ℓ]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list V) s) A)
    (define α (-α.x/c x))
    (define-values (ςs δσ₀ δσₖ δM) (⟦k⟧ A Γ 𝒞 (σ⊔ σ α V #t) M))
    (values ςs (σ⊔ δσ₀ α V #t) δσₖ δM)))
