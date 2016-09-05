#lang typed/racket/base

(provide (all-defined-out))

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "utils.rkt"
         "base.rkt"
         "app.rkt"
         racket/set
         racket/match)

;; Base continuation that returns locally finished configuration
(define/memo (rt [αₖ : -αₖ]) : -⟦k⟧!
  (λ (A Γ 𝒞 Σ)
    (match-define (-Σ _ _ M) Σ)
    (⊔! M αₖ (-ΓA Γ A))
    {set (-ς↓ αₖ Γ A)}))

;; Application
(define/memo (ap∷ [Ws : (Listof -W¹)]
                  [⟦e⟧s : (Listof -⟦e⟧!)]
                  [ρ : -ρ]
                  [l : -l]
                  [ℓ : -ℓ]
                  [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define Ws* (cons (-W¹ V s) Ws))
       (match ⟦e⟧s
         ['()
          (match-define (cons Wₕ Wₓs) (reverse Ws*))
          (app l ℓ Wₕ Wₓs Γ 𝒞 Σ ⟦k⟧)]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (⟦e⟧ ρ Γ 𝒞 Σ (ap∷ Ws* ⟦e⟧s* ρ l ℓ ⟦k⟧))])]
      [_
       (⟦k⟧ (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 Σ)])))

;; Conditional
(define/memo (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧!] [⟦e⟧₂ : -⟦e⟧!] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (match-define (-Σ _ _ M) Σ)
       (define-values (Γ₁ Γ₂) (Γ+/-V M Γ V s))
       (∪ (with-Γ Γ₁ (⟦e⟧₁ ρ Γ₁ 𝒞 Σ ⟦k⟧))
          (with-Γ Γ₂ (⟦e⟧₂ ρ Γ₂ 𝒞 Σ ⟦k⟧)))]
      [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 Σ)])))

;; begin
(define/memo (bgn∷ [⟦e⟧s : (Listof -⟦e⟧!)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
       (⟦e⟧ ρ Γ 𝒞 Σ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

;; begin0, waiting on first value
(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧!)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
       (⟦e⟧ ρ Γ 𝒞 Σ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

;; begin0, already have first value
(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧!)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
       (⟦e⟧ ρ Γ 𝒞 Σ (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧)))]))

;; set!
(define/memo (set!∷ [α : -α] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (match-define (-Σ σ _ _) Σ)
       (σ⊔! σ α V #f)
       (⟦k⟧ -Void/W Γ 𝒞 Σ)]
      [_
       (⟦k⟧ (-blm 'TODO 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))) Γ 𝒞 Σ)])))

;; let-values
(define/memo (let∷ [l : -l]
                   [xs : (Listof Var-Name)]
                   [⟦bnd⟧s : (Listof (Pairof (Listof Var-Name) -⟦e⟧!))]
                   [bnd-Ws : (Listof (List Var-Name -V -s))]
                   [⟦e⟧ : -⟦e⟧!]
                   [ρ : -ρ]
                   [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
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
          (match-define (-Σ σ _ _) Σ)
          (define-values (ρ* Γ*) ; with side effect widening store
            (for/fold ([ρ : -ρ ρ] [Γ : -Γ Γ])
                      ([bnd-W bnd-Ws])
              (match-define (list (? Var-Name? x) (? -V? Vₓ) (? -s? sₓ)) bnd-W)
              (define α (-α.x x 𝒞))
              (σ⊔! σ α Vₓ #t)
              (values (ρ+ ρ x α)
                      (-Γ-with-aliases Γ x sₓ))))
          (⟦e⟧ ρ* Γ* 𝒞 Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ Γ 𝒞 Σ (let∷ l xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'let-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 Σ)])))

;; letrec-values
(define/memo (letrec∷ [l : -l]
                      [xs : (Listof Var-Name)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Var-Name) -⟦e⟧!))]
                      [⟦e⟧ : -⟦e⟧!]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W Vs s) A)
    (define n (length xs))
    (cond
      [(= n (length Vs))
       (match-define (-Σ σ _ _) Σ)
       (define Γ* ; with side effect widening store
         (for/fold ([Γ : -Γ Γ])
                   ([x xs] [Vₓ Vs] [sₓ (split-values s n)])
           (define α (-α.x x 𝒞))
           (σ⊔! σ α Vₓ #t)
           (Γ+ (-Γ-with-aliases Γ x sₓ) (-?@ 'defined? (-x x)))))
       (match ⟦bnd⟧s
         ['()
          (⟦e⟧ ρ Γ* 𝒞 Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ Γ* 𝒞 Σ (letrec∷ l xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'letrec-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 Σ)])))

;; μ/c
(define/memo (μ/c∷ [l : -l] [x : -ℓ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list V) s) A)
    (match-define (-Σ σ _ _) Σ)
    (define α (-α.x/c x))
    (σ⊔! σ α V #t)
    (⟦k⟧ A Γ 𝒞 Σ)))

;; Non-dependent contract domain
(define/memo (-->.dom∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [⟦c⟧s : (Listof -⟦e⟧!)]
                       [⟦d⟧  : -⟦e⟧!]
                       [ρ   : -ρ]
                       [ℓ   : -ℓ]
                       [⟦k⟧  : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list V) s) A)
    (define Ws* (cons (-W¹ V s) Ws))
    (match ⟦c⟧s
      ['()            (⟦d⟧ ρ Γ 𝒞 Σ (-->.rng∷ l Ws* ℓ ⟦k⟧))]
      [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ Γ 𝒞 Σ (-->.dom∷ l Ws* ⟦c⟧s* ⟦d⟧ ρ ℓ ⟦k⟧))])))

;; Non-dependent contract range
(define/memo (-->.rng∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [ℓ   : -ℓ]
                       [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-Σ σ _ _) Σ)
    (match-define (-W (list D) d) A)
    (define β (-α.rng ℓ 𝒞))
    (σ⊔! σ β D #t)
    (define-values (αs cs) ; with side effect widening store
      (for/fold ([αs : (Listof -α.dom) '()]
                 [cs : (Listof -s) '()])
                ([(W i) (in-indexed Ws)])
        (match-define (-W C c) W)
        (define α (-α.dom ℓ 𝒞 i))
        (σ⊔! σ α C #t)
        (values (cons α αs) (cons c cs))))
    (define G (-W (list (-=> αs β ℓ)) (-?-> cs d)))
    (⟦k⟧ G Γ 𝒞 Σ)))

(: mk-=>i! : -σ -Γ -𝒞 (Listof -W¹) -Clo (Option -λ) -ℓ → (Values -V -s))
;; Given *reversed* list of contract domains and range-maker, create dependent contract
(define (mk-=>i! σ Γ 𝒞 Ws Mk-D mk-d ℓ)
  (define-values (αs cs) ; with side effect widening store
    (for/fold ([αs : (Listof -α.dom) '()]
               [cs : (Listof -s) '()])
              ([(W i) (in-indexed Ws)])
      (match-define (-W¹ C c) W)
      (define α (-α.dom ℓ 𝒞 (assert i exact-nonnegative-integer?))) ; why TR randomly can't prove `i`???
      (σ⊔! σ α C #t)
      (values (cons α αs) (cons c cs))))
  (define β (-α.rng ℓ 𝒞))
  (define G (-=>i αs β ℓ))
  (define g (-?->i cs mk-d))
  (σ⊔! σ β G #t)
  (values G g))

;; Dependent contract
(define/memo (-->i∷ [Ws  : (Listof -W¹)]
                    [⟦c⟧s : (Listof -⟦e⟧!)]
                    [ρ   : -ρ]
                    [Mk-D : -Clo]
                    [mk-d : (Option -λ)]
                    [ℓ    : -ℓ]
                    [⟦k⟧  : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list C) c) A)
    (define Ws* (cons (-W¹ C c) Ws))
    (match ⟦c⟧s
      ['()
       (match-define (-Σ σ _ _) Σ)
       (define-values (G g) (mk-=>i! σ Γ 𝒞 Ws* Mk-D mk-d ℓ))
       (⟦k⟧ (-W (list G) g) Γ 𝒞 Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ Γ 𝒞 Σ (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

;; Clean up path-condition
(define/memo (rst∷ [xs : (℘ Var-Name)] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (λ (A Γ 𝒞 Σ) (⟦k⟧ A (Γ↓ Γ xs) 𝒞 Σ)))

;; case-> contract
(define/memo (case->∷ [l : -l]
                      [ℓ : -ℓ]
                      [Clauses : (Listof (Listof -W¹))]
                      [Cs : (Listof -W¹)]
                      [⟦c⟧s : (Listof -⟦e⟧!)]
                      [⟦clause⟧s : (Listof (Listof -⟦e⟧!))]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (define Clauses* (cons Cs* Clauses))
       (match ⟦clause⟧s
         ['()                      (error 'case->∷ "TODO")]
         [(cons ⟦clause⟧ ⟦clause⟧s*) (error 'case->∷ "TODO")])]
      [(cons ⟦c⟧* ⟦c⟧s*)
       (⟦c⟧* ρ Γ 𝒞 Σ (case->∷ l ℓ Clauses Cs* ⟦c⟧s* ⟦clause⟧s ρ ⟦k⟧))])))

;; struct/c contract
(define/memo (struct/c∷ [ℓ : -ℓ]
                        [si : -struct-info]
                        [Cs : (Listof -W¹)]
                        [⟦c⟧s : (Listof -⟦e⟧!)]
                        [ρ : -ρ]
                        [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (match-define (-Σ σ _ _) Σ)
       (define-values (αs cs flat?) ; with side effect widening store
         (for/fold ([αs : (Listof -α.struct/c) '()]
                    [cs : (Listof -s) '()]
                    [flat? : Boolean #t])
                   ([(W i) (in-indexed Cs*)])
           (match-define (-W¹ C c) W)
           (define α (-α.struct/c ℓ 𝒞 (assert i exact-nonnegative-integer?)))
           (σ⊔! σ α C #t)
           (values (cons α αs)
                   (cons c cs)
                   (and flat? (C-flat? C)))))
       (define W (-W (list (-St/C flat? si αs)) (-?struct/c si cs)))
       (⟦k⟧ W Γ 𝒞 Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ Γ 𝒞 Σ (struct/c∷ ℓ si Cs* ⟦c⟧s* ρ ⟦k⟧))])))

;; define
(define/memo (def∷ [l : -l]
                   [αs : (Listof -α)]
                   [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (define n (length αs))
    (match-define (-W Vs s) A)
    (cond
      [(= n (length Vs))
       (match-define (-Σ σ _ _) Σ)
       (for ([α αs] [V Vs])
         (σ⊔! σ α V #t))
       (⟦k⟧ -Void/W Γ 𝒞 Σ)]
      [else
       (define blm (-blm l 'define-values
                         (list (format-symbol "~a values" n))
                         (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm Γ 𝒞 Σ)])))

;; provide with contract
(define/memo (dec∷ [ℓ : -ℓ]
                   [𝒾 : -𝒾]
                   [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (define l (-𝒾-ctx 𝒾))
  (define l³ (-l³ l 'dummy l))
  (with-error-handling (⟦k⟧ A Γ 𝒞 Σ)
    (match-define (-W (list C) c) A)
    (match-define (-Σ σ _ _) Σ)
    (define W-C (-W¹ C c))
    (define-values (Vs _) (σ@ σ (-α.def 𝒾)))
    (for/union : (℘ -ς) ([V Vs])
      (mon l³ ℓ W-C (-W¹ V 𝒾) Γ 𝒞 Σ ⟦k⟧))))
