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

;; set!
(define/memo (set!∷ [α : ⟪α⟫] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (σ⊕! Σ α V #:mutating? #t)
       (define s
         (match (⟪α⟫->-α α)
           [(-α.x x _) (canonicalize Γ x)]
           [(? -𝒾? 𝒾) 𝒾]))
       (⟦k⟧ -Void/W ($+ $ s V) Γ ⟪ℋ⟫ Σ)]
      [_
       (define blm
         (-blm 'TODO 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs))) +ℓ₀))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; letrec-values
(define/memo (letrec∷ [ℓ : ℓ]
                      [xs : (Listof Symbol)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                      [⟦e⟧ : -⟦e⟧]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
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
           (σ⊕! Σ α (V+ σ Vₓ (predicates-of Γ sₓ)))
           (σ-remove! Σ α -undefined)
           (-Γ-with-aliases Γ x sₓ)))
       (match ⟦bnd⟧s
         ['()
          (⟦e⟧ ρ $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ $ Γ* ⟪ℋ⟫ Σ (letrec∷ ℓ xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm (ℓ-src ℓ) 'letrec-values
               (list (format-symbol "~a values" (length xs)))
               (list (format-symbol "~a values" (length Vs)))
               +ℓ₀))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; μ/c
(define/memo (μ/c∷ [x : Symbol] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W (list V) s) A)
    (define α (-α->⟪α⟫ (-α.x/c x)))
    (σ⊕! Σ α V)
    (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))

;; Non-dependent contract domain
(define/memo (-->.dom∷ [Ws  : (Listof -W¹)]
                       [⟦c⟧s : (Listof -⟦e⟧)]
                       [⟦d⟧  : -⟦e⟧]
                       [ρ   : -ρ]
                       [ℓ   : ℓ]
                       [⟦k⟧  : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
    (match-define (-W (list V) s) A)
    (define Ws* (cons (-W¹ V s) Ws))
    (match ⟦c⟧s
      ['()            (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ Ws* ℓ ⟦k⟧))]
      [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ Ws* ⟦c⟧s* ⟦d⟧ ρ ℓ ⟦k⟧))])))

;; Non-dependent contract range
(define/memo (-->.rng∷ [Ws : (Listof -W¹)]
                       [ℓₐ : ℓ]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws)
    (match-define (-W (list D) d) A)
    (define β (-α->⟪α⟫ (or (keep-if-const d) (-α.rng ℓₐ #|TODO right?|# ⟪ℋ⟫))))
    (σ⊕! Σ β D)
    (define-values (αs cs) ; with side effect widening store
      (for/fold ([αs : (Listof ⟪α⟫) '()]
                 [cs : (Listof -s) '()])
                ([(W i) (in-indexed Ws)] #:when (exact-nonnegative-integer? i))
        (match-define (-W¹ C c) W)
        (define α (-α->⟪α⟫ (or (keep-if-const c) (-α.dom ℓₐ ⟪ℋ⟫ i))))
        (σ⊕! Σ α C)
        (values (cons α αs) (cons c cs))))
    (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
      (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
        (cons (cast α ⟪α⟫) (ℓ-with-id ℓₐ i))))
    (define βℓ (cons β (ℓ-with-id ℓₐ (length αs))))
    (define G (-W (list (-=> αℓs βℓ ℓₐ)) (-?-> cs d ℓₐ)))
    (⟦k⟧ G $ Γ ⟪ℋ⟫ Σ)))

(: mk-=>i! : -Σ -Γ -⟪ℋ⟫ (Listof -W¹) -Clo -λ ℓ → (Values -V -s))
;; Given *reversed* list of contract domains and range-maker, create dependent contract
(define (mk-=>i! Σ Γ ⟪ℋ⟫ Ws Mk-D mk-d ℓₐ)
  (define-values (αs cs) ; with side effect widening store
    (for/fold ([αs : (Listof ⟪α⟫) '()]
               [cs : (Listof -s) '()])
              ([(W i) (in-indexed Ws)])
      (match-define (-W¹ C c) W)
      (define α
        (-α->⟪α⟫ (or (keep-if-const c)
                      (-α.dom ℓₐ ⟪ℋ⟫ (assert i exact-nonnegative-integer?)))))
      (σ⊕! Σ α C)
      (values (cons α αs) (cons c cs))))
  (define β (-α->⟪α⟫ (or (keep-if-const mk-d) (-α.rng ℓₐ ⟪ℋ⟫))))
  (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
    (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
      (cons (cast α ⟪α⟫) (ℓ-with-id ℓₐ i))))
  (define G (-=>i αℓs (list Mk-D mk-d (ℓ-with-id ℓₐ (length αs))) ℓₐ))
  (define g (-?->i cs mk-d ℓₐ))
  (σ⊕! Σ β Mk-D)
  (values G g))

;; Dependent contract
(define/memo (-->i∷ [Ws  : (Listof -W¹)]
                    [⟦c⟧s : (Listof -⟦e⟧)]
                    [ρ   : -ρ]
                    [Mk-D : -Clo]
                    [mk-d : -λ]
                    [ℓ    : ℓ]
                    [⟦k⟧  : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ Mk-D)
    (match-define (-W (list C) c) A)
    (define Ws* (cons (-W¹ C c) Ws))
    (match ⟦c⟧s
      ['()
       (define-values (G g) (mk-=>i! Σ Γ ⟪ℋ⟫ Ws* Mk-D mk-d ℓ))
       (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

;; case-> contract
(define/memo (case->∷ [ℓ : ℓ]
                      [Clauses : (Listof (Listof -W¹))]
                      [Cs : (Listof -W¹)]
                      [⟦c⟧s : (Listof -⟦e⟧)]
                      [⟦clause⟧s : (Listof (Listof -⟦e⟧))]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
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
       (⟦c⟧* ρ $ Γ ⟪ℋ⟫ Σ (case->∷ ℓ Clauses Cs* ⟦c⟧s* ⟦clause⟧s ρ ⟦k⟧))])))

;; struct/c contract
(define/memo (struct/c∷ [ℓ₁ : ℓ]
                        [𝒾 : -𝒾]
                        [Cs : (Listof -W¹)]
                        [⟦c⟧s : (Listof -⟦e⟧)]
                        [ρ : -ρ]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (#;Cs ρ)
    (match-define (-W (list C) c) A)
    (define Cs* (cons (-W¹ C c) Cs))
    (match ⟦c⟧s
      ['()
       (define-values (αs cs flat?) ; with side effect widening store
         (for/fold ([αs : (Listof ⟪α⟫) '()]
                    [cs : (Listof -s) '()]
                    [flat? : Boolean #t])
                   ([(W i) (in-indexed Cs*)])
           (match-define (-W¹ C c) W)
           (define α
             (-α->⟪α⟫ (or (keep-if-const c)
                          (-α.struct/c ℓ₁ ⟪ℋ⟫ (assert i exact-nonnegative-integer?)))))
           (σ⊕! Σ α C)
           (values (cons α αs)
                   (cons c cs)
                   (and flat? (C-flat? C)))))
       (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
         (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
           (cons (cast α ⟪α⟫) (ℓ-with-id ℓ₁ i))))
       (define W (-W (list (-St/C flat? 𝒾 αℓs)) (-?struct/c 𝒾 cs)))
       (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ)]
      [(cons ⟦c⟧ ⟦c⟧s*)
       (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (struct/c∷ ℓ₁ 𝒾 Cs* ⟦c⟧s* ρ ⟦k⟧))])))

;; define
(define/memo (def∷ [l : -l]
                   [αs : (Listof ⟪α⟫)]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (define n (length αs))
    (match-define (-W Vs s) A)
    (cond
      [(= n (length Vs))
       (for ([α : ⟪α⟫ αs] [V Vs])
         (σ⊕! Σ α V))
       (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
      [else
       (define blm
         (-blm l 'define-values
               (list (format-symbol "~a values" n))
               (list (format-symbol "~a values" (length Vs)))
               +ℓ₀))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; provide with contract
(define/memo (dec∷ [ℓ : ℓ]
                   [𝒾 : -𝒾]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define l (-𝒾-ctx 𝒾))
  (define l³ (-l³ l 'dummy l))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W (list C) c) A)
    (match-define (-Σ σ _ _) Σ)
    (define W-C (-W¹ C c))
    (define Vs (σ@ σ (-α->⟪α⟫ 𝒾)))
    (for/union : (℘ -ς) ([V Vs])
      (mon l³ $ (-ℒ (seteq ℓ) ℓ) W-C (-W¹ V 𝒾) Γ ⟪ℋ⟫ Σ
           (def∷ l (list (-α->⟪α⟫ (-α.wrp 𝒾))) ⟦k⟧)))))
