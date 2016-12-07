#lang typed/racket/base

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "utils.rkt"
         "base.rkt"
         "app.rkt"
         racket/set
         racket/match)

(provide (all-defined-out)
         (all-from-out "app.rkt"))

;; begin0, waiting on first value
(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧!)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

;; begin0, already have first value
(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧!)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧)))]))

;; set!
(define/memo (set!∷ [α : -⟪α⟫] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (match-define (-Σ σ _ _) Σ)
       (σ⊕! σ α V #:mutating? #t)
       (define s
         (match (-⟪α⟫->-α α)
           [(-α.x x _) (canonicalize Γ x)]
           [(-α.def 𝒾) 𝒾]))
       (⟦k⟧ -Void/W ($+ $ s V) Γ ⟪ℋ⟫ Σ)]
      [_
       (define blm
         (-blm 'TODO 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; letrec-values
(define/memo (letrec∷ [l : -l]
                      [xs : (Listof Symbol)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧!))]
                      [⟦e⟧ : -⟦e⟧!]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (define n (length xs))
    (cond
      [(= n (length Vs))
       (match-define (-Σ σ _ _) Σ)
       (define Γ* ; with side effect widening store
         (for/fold ([Γ : -Γ Γ])
                   ([x xs] [Vₓ Vs] [sₓ (split-values s n)])
           (define α (ρ@ ρ x) #;(-α.x x #|TODO right?|# ⟪ℋ⟫))
           (σ⊕! σ α (V+ σ Vₓ (predicates-of Γ sₓ)))
           (σ-remove! σ α -undefined)
           (-Γ-with-aliases Γ x sₓ)))
       (match ⟦bnd⟧s
         ['()
          (⟦e⟧ ρ $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ $ Γ* ⟪ℋ⟫ Σ (letrec∷ l xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'letrec-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; μ/c
(define/memo (μ/c∷ [l : -l] [x : Symbol] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W (list V) s) A)
    (match-define (-Σ σ _ _) Σ)
    (define α (-α->-⟪α⟫ (-α.x/c x)))
    (σ⊕! σ α V)
    (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))

;; Non-dependent contract domain
(define/memo (-->.dom∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [⟦c⟧s : (Listof -⟦e⟧!)]
                       [⟦d⟧  : -⟦e⟧!]
                       [ρ   : -ρ]
                       [ℓ   : -ℓ]
                       [⟦k⟧  : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
    (match-define (-W (list V) s) A)
    (define Ws* (cons (-W¹ V s) Ws))
    (match ⟦c⟧s
      ['()            (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ l Ws* ℓ ⟦k⟧))]
      [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ l Ws* ⟦c⟧s* ⟦d⟧ ρ ℓ ⟦k⟧))])))

;; Non-dependent contract range
(define/memo (-->.rng∷ [l   : -l]
                       [Ws  : (Listof -W¹)]
                       [ℓ   : -ℓ]
                       [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws)
    (match-define (-Σ σ _ _) Σ)
    (match-define (-W (list D) d) A)
    (define β (-α->-⟪α⟫ (or (keep-if-const d) (-α.rng ℓ #|TODO right?|# ⟪ℋ⟫))))
    (σ⊕! σ β D)
    (define-values (αs cs) ; with side effect widening store
      (for/fold ([αs : (Listof -⟪α⟫) '()]
                 [cs : (Listof -s) '()])
                ([(W i) (in-indexed Ws)] #:when (exact-nonnegative-integer? i))
        (match-define (-W¹ C c) W)
        (define α (-α->-⟪α⟫ (or (keep-if-const c) (-α.dom ℓ ⟪ℋ⟫ i))))
        (σ⊕! σ α C)
        (values (cons α αs) (cons c cs))))
    (define αℓs : (Listof (Pairof -⟪α⟫ -ℓ))
      (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
        (cons (cast α -⟪α⟫) (+ℓ/ctc ℓ i))))
    (define βℓ (cons β (+ℓ/ctc ℓ (length αs))))
    (define G (-W (list (-=> αℓs βℓ ℓ)) (-?-> cs d ℓ)))
    (⟦k⟧ G $ Γ ⟪ℋ⟫ Σ)))

(: mk-=>i! : -σ -Γ -⟪ℋ⟫ (Listof -W¹) -Clo -λ -ℓ → (Values -V -s))
;; Given *reversed* list of contract domains and range-maker, create dependent contract
(define (mk-=>i! σ Γ ⟪ℋ⟫ Ws Mk-D mk-d ℓ)
  (define-values (αs cs) ; with side effect widening store
    (for/fold ([αs : (Listof -⟪α⟫) '()]
               [cs : (Listof -s) '()])
              ([(W i) (in-indexed Ws)])
      (match-define (-W¹ C c) W)
      (define α
        (-α->-⟪α⟫ (or (keep-if-const c)
                      (-α.dom ℓ ⟪ℋ⟫ (assert i exact-nonnegative-integer?)))))
      (σ⊕! σ α C)
      (values (cons α αs) (cons c cs))))
  (define β (-α->-⟪α⟫ (or (keep-if-const mk-d) (-α.rng ℓ ⟪ℋ⟫))))
  (define αℓs : (Listof (Pairof -⟪α⟫ -ℓ))
    (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
      (cons (cast α -⟪α⟫) (+ℓ/ctc ℓ i))))
  (define G (-=>i αℓs (list Mk-D mk-d (+ℓ/ctc ℓ (length αs))) ℓ))
  (define g (-?->i cs mk-d ℓ))
  (σ⊕! σ β Mk-D)
  (values G g))

;; Dependent contract
(define/memo (-->i∷ [Ws  : (Listof -W¹)]
                    [⟦c⟧s : (Listof -⟦e⟧!)]
                    [ρ   : -ρ]
                    [Mk-D : -Clo]
                    [mk-d : -λ]
                    [ℓ    : -ℓ]
                    [⟦k⟧  : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ Mk-D)
    (match-define (-W (list C) c) A)
    (define Ws* (cons (-W¹ C c) Ws))
    (match ⟦c⟧s
      ['()
       (match-define (-Σ σ _ _) Σ)
       (define-values (G g) (mk-=>i! σ Γ ⟪ℋ⟫ Ws* Mk-D mk-d ℓ))
       (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

;; Clean up path-condition
(define/memo (rst∷ [xs : (℘ Symbol)] [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (⟦k⟧ A $ (Γ↓ Γ xs) ⟪ℋ⟫ Σ)))

;; case-> contract
(define/memo (case->∷ [l : -l]
                      [ℓ : -ℓ]
                      [Clauses : (Listof (Listof -W¹))]
                      [Cs : (Listof -W¹)]
                      [⟦c⟧s : (Listof -⟦e⟧!)]
                      [⟦clause⟧s : (Listof (Listof -⟦e⟧!))]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (define Clauses* (cons Cs* Clauses))
       (match ⟦clause⟧s
         ['()                      (error 'case->∷ "TODO")]
         [(cons ⟦clause⟧ ⟦clause⟧s*) (error 'case->∷ "TODO")])]
      [(cons ⟦c⟧* ⟦c⟧s*)
       (⟦c⟧* ρ $ Γ ⟪ℋ⟫ Σ (case->∷ l ℓ Clauses Cs* ⟦c⟧s* ⟦clause⟧s ρ ⟦k⟧))])))

;; struct/c contract
(define/memo (struct/c∷ [ℓ : -ℓ]
                        [𝒾 : -𝒾]
                        [Cs : (Listof -W¹)]
                        [⟦c⟧s : (Listof -⟦e⟧!)]
                        [ρ : -ρ]
                        [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (#;Cs ρ)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (match-define (-Σ σ _ _) Σ)
       (define-values (αs cs flat?) ; with side effect widening store
         (for/fold ([αs : (Listof -⟪α⟫) '()]
                    [cs : (Listof -s) '()]
                    [flat? : Boolean #t])
                   ([(W i) (in-indexed Cs*)])
           (match-define (-W¹ C c) W)
           (define α
             (-α->-⟪α⟫ (or (keep-if-const c)
                           (-α.struct/c ℓ ⟪ℋ⟫ (assert i exact-nonnegative-integer?)))))
           (σ⊕! σ α C)
           (values (cons α αs)
                   (cons c cs)
                   (and flat? (C-flat? C)))))
       (define αℓs : (Listof (Pairof -⟪α⟫ -ℓ))
         (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
           (cons (cast α -⟪α⟫) (+ℓ/ctc ℓ i))))
       (define W (-W (list (-St/C flat? 𝒾 αℓs)) (-?struct/c 𝒾 cs)))
       (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (struct/c∷ ℓ 𝒾 Cs* ⟦c⟧s* ρ ⟦k⟧))])))

;; define
(define/memo (def∷ [l : -l]
                   [αs : (Listof -⟪α⟫)]
                   [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (define n (length αs))
    (match-define (-W Vs s) A)
    (cond
      [(= n (length Vs))
       (match-define (-Σ σ _ _) Σ)
       (for ([α : -⟪α⟫ αs] [V Vs])
         (σ⊕! σ α V))
       (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
      [else
       (define blm
         (-blm l 'define-values
               (list (format-symbol "~a values" n))
               (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; provide with contract
(define/memo (dec∷ [ℓ : -ℓ]
                   [𝒾 : -𝒾]
                   [⟦k⟧ : -⟦k⟧!]) : -⟦k⟧!
  (define l (-𝒾-ctx 𝒾))
  (define l³ (-l³ l 'dummy l))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W (list C) c) A)
    (match-define (-Σ σ _ _) Σ)
    (define W-C (-W¹ C c))
    (define Vs (σ@ σ (-α->-⟪α⟫ (-α.def 𝒾))))
    (for/union : (℘ -ς) ([V Vs])
      (mon l³ $ (-ℒ (set ℓ) ℓ) W-C (-W¹ V 𝒾) Γ ⟪ℋ⟫ Σ
           (def∷ l (list (-α->-⟪α⟫ (-α.wrp 𝒾))) ⟦k⟧)))))
