#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "base.rkt"
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
                  [l : -l]
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
(define/memo (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
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
(define/memo (let∷ [l : -l]
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
          (with-δσ δσ
            (⟦e⟧ ρ* Γ* 𝒞 σ* M ⟦k⟧))]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ Γ 𝒞 σ M (let∷ l xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'let-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 σ M)])))

;; letrec-values
(define/memo (letrec∷ [l : -l]
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
       (with-δσ δσ
         (match ⟦bnd⟧s
           ['()
            (⟦e⟧ ρ Γ* 𝒞 σ* M ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ Γ* 𝒞 σ* M (letrec∷ l xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))]))]
      [else
       (define blm
         (-blm l 'letrec-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 σ M)])))

;; μ/c
(define/memo (μ/c∷ [l : -l] [x : -ℓ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list V) s) A)
    (define α (-α.x/c x))
    (define-values (ςs δσ₀ δσₖ δM) (⟦k⟧ A Γ 𝒞 (σ⊔ σ α V #t) M))
    (values ςs (σ⊔ δσ₀ α V #t) δσₖ δM)))

;; Non-dependent contract domain
(define/memo (-->.dom∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [⟦c⟧s : (Listof -⟦e⟧)]
                       [⟦d⟧  : -⟦e⟧]
                       [ρ   : -ρ]
                       [ℓ   : -ℓ]
                       [⟦k⟧  : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list V) s) A)
    (define Ws* (cons (-W¹ V s) Ws))
    (match ⟦c⟧s
      ['()            (⟦d⟧ ρ Γ 𝒞 σ M (-->.rng∷ l Ws* ℓ ⟦k⟧))]
      [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ Γ 𝒞 σ M (-->.dom∷ l Ws* ⟦c⟧s* ⟦d⟧ ρ ℓ ⟦k⟧))])))

;; Non-dependent contract range
(define/memo (-->.rng∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [ℓ   : -ℓ]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list D) d) A)
    (define β (-α.rng ℓ 𝒞))
    (define-values (σ* δσ αs cs)
      (for/fold ([σ  : -σ  (σ⊔ σ  β D #t)]
                 [δσ : -Δσ (σ⊔ ⊥σ β D #t)]
                 [αs : (Listof -α.dom) '()]
                 [cs : (Listof -s) '()])
                ([(W i) (in-indexed Ws)])
        (match-define (-W C c) W)
        (define α (-α.dom ℓ 𝒞 i))
        (values (σ⊔ σ  α C #t)
                (σ⊔ δσ α C #t)
                (cons α αs)
                (cons c cs))))
    (define G (-W (list (-=> αs β ℓ)) (-?-> cs d)))
    (with-δσ δσ (⟦k⟧ G Γ 𝒞 σ* M))))

(: mk-=>i : -Γ -𝒞 (Listof -W¹) -Clo (Option -λ) -ℓ → (Values -V -s -Δσ))
;; Given *reversed* list of contract domains and range-maker, create dependent contract
(define (mk-=>i Γ 𝒞 Ws Mk-D mk-d ℓ)
  (define-values (δσ αs cs)
    (for/fold ([δσ : -Δσ ⊥σ]
               [αs : (Listof -α.dom) '()]
               [cs : (Listof -s) '()])
              ([(W i) (in-indexed Ws)])
      (match-define (-W¹ C c) W)
      (define α (-α.dom ℓ 𝒞 (assert i exact-nonnegative-integer?))) ; why TR randomly can't prove `i`???
      (values (σ⊔ δσ α C #t) (cons α αs) (cons c cs))))
  (define β (-α.rng ℓ 𝒞))
  (define G (-=>i αs β ℓ))
  (define g (-?->i cs mk-d))
  (values G g (σ⊔ δσ β G #t)))

;; Dependent contract
(define/memo (-->i∷ [Ws  : (Listof -W¹)]
                    [⟦c⟧s : (Listof -⟦e⟧)]
                    [ρ   : -ρ]
                    [Mk-D : -Clo]
                    [mk-d : (Option -λ)]
                    [ℓ    : -ℓ]
                    [⟦k⟧  : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list C) c) A)
    (define Ws* (cons (-W¹ C c) Ws))
    (match ⟦c⟧s
      ['()
       (define-values (G g δσ) (mk-=>i Γ 𝒞 Ws* Mk-D mk-d ℓ))
       (with-δσ δσ (⟦k⟧ (-W (list G) g) Γ 𝒞 (⊔σ σ δσ) M))]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ Γ 𝒞 σ M (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

;; Clean up path-condition
(define/memo (rst∷ [xs : (℘ Var-Name)] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (λ (A Γ 𝒞 σ M) (⟦k⟧ A (Γ↓ Γ xs) 𝒞 σ M)))

;; case-> contract
(define/memo (case->∷ [l : -l]
                      [ℓ : -ℓ]
                      [Clauses : (Listof (Listof -W¹))]
                      [Cs : (Listof -W¹)]
                      [⟦c⟧s : (Listof -⟦e⟧)]
                      [⟦clause⟧s : (Listof (Listof -⟦e⟧))]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (define Clauses* (cons Cs* Clauses))
       (match ⟦clause⟧s
         ['()                      (error 'case->∷ "TODO")]
         [(cons ⟦clause⟧ ⟦clause⟧s*) (error 'case->∷ "TODO")])]
      [(cons ⟦c⟧* ⟦c⟧s*)
       (⟦c⟧* ρ Γ 𝒞 σ M (case->∷ l ℓ Clauses Cs* ⟦c⟧s* ⟦clause⟧s ρ ⟦k⟧))])))

;; struct/c contract
(define/memo (struct/c∷ [ℓ : -ℓ]
                        [si : -struct-info]
                        [Cs : (Listof -W¹)]
                        [⟦c⟧s : (Listof -⟦e⟧)]
                        [ρ : -ρ]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (define-values (σ* δσ αs cs flat?)
         (for/fold ([σ  : -σ  σ]
                    [δσ : -Δσ ⊥σ]
                    [αs : (Listof -α.struct/c) '()]
                    [cs : (Listof -s) '()]
                    [flat? : Boolean #t])
                   ([(W i) (in-indexed Cs*)])
           (match-define (-W¹ C c) W)
           (define α (-α.struct/c ℓ 𝒞 (assert i exact-nonnegative-integer?)))
           (values (σ⊔ σ  α C #t)
                   (σ⊔ δσ α C #t)
                   (cons α αs)
                   (cons c cs)
                   (and flat? (C-flat? C)))))
       (define W (-W (list (-St/C flat? si αs)) (-?struct/c si cs)))
       (with-δσ δσ (⟦k⟧ W Γ 𝒞 σ M))]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ Γ 𝒞 σ M (struct/c∷ ℓ si Cs* ⟦c⟧s* ρ ⟦k⟧))])))

;; define
(define/memo (def∷ [l : -l]
                   [αs : (Listof -α)]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (define n (length αs))
    (match-define (-W Vs s) A)
    (cond
      [(= n (length Vs))
       (define-values (σ* δσ)
         (for/fold ([σ  : -σ  σ]
                    [δσ : -Δσ ⊥σ])
                   ([α αs] [V Vs])
           (values (σ⊔  σ α V #t)
                   (σ⊔ δσ α V #t))))
       (with-δσ δσ (⟦k⟧ -Void/W Γ 𝒞 σ* M))]
      [else
       (define blm (-blm l 'define-values
                         (list (format-symbol "~a values" n))
                         (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 σ M)])))

;; provide with contract
(define/memo (dec∷ [ℓ : -ℓ]
                   [𝒾 : -𝒾]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define l (-𝒾-ctx 𝒾))
  (define l³ (-l³ l 'dummy l))
  (with-error-handling (⟦k⟧ A Γ 𝒞 σ M)
    (match-define (-W (list C) c) A)
    (define W-C (-W¹ C c))
    (define-values (Vs _) (σ@ σ (-α.def 𝒾)))
    (for*/ans ([V Vs])
      (mon l³ ℓ W-C (-W¹ V 𝒾) Γ 𝒞 σ M ⟦k⟧))))
