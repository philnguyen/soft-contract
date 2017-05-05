#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/set
         racket/match
         typed/racket/unit
         racket/splicing
         syntax/parse/define
         set-extras
         "../settings.rkt"
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "../proof-relation/signatures.rkt"
         "signatures.rkt"
         )

(provide kont@)

(define-unit kont@
  (import compile^ app^ mon^ proof-system^ widening^ memoize^)
  (export kont^)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Macros
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (splicing-let-syntax ([compute-frame-roots
                         (syntax-parser
                           [(_) #'∅eq]
                           [(_ root:id) #'(->⟪α⟫s root)]
                           [(_ root:id ...) #'(∪ (->⟪α⟫s root) ...)])])
    (define-simple-macro (make-frame (⟦k⟧:id A:id $:id Γ:id ⟪ℋ⟫:id Σ:id)
                           #:roots (root:id ...)
                           e ...)
      (let ([αₖ (⟦k⟧->αₖ ⟦k⟧)]
            [frame-roots (compute-frame-roots root ...)]
            [tail-roots (⟦k⟧->roots ⟦k⟧)])
        (define ⟦k⟧₀ (rt αₖ))
        (define ⟦k⟧* : -⟦k⟧
          (λ (A $ Γ ⟪ℋ⟫ Σ)
            (cond [(-blm? A) (⟦k⟧₀ A $ Γ ⟪ℋ⟫ Σ)]
                  [else e ...])))
        (set-⟦k⟧->αₖ! ⟦k⟧* αₖ)
        (add-⟦k⟧-roots! ⟦k⟧* (∪ frame-roots tail-roots))
        ⟦k⟧*)))

  (define-simple-macro (define-frame (φ:id [arg:id (~literal :) τ] ...) e ...)
    (define/memo (φ [arg : τ] ...) : -⟦k⟧ e ...))

  (splicing-local
      ((define print-cache : (HashTable -blm Void) (make-hash)))

    ;; Base continuation that returns locally finished configuration
    (define-frame (rt [αₖ : -αₖ])
      (define ⟦k⟧ : -⟦k⟧
        (λ (A $ Γ ⟪ℋ⟫ Σ)
          (define (maybe-print-blame)
            (when (and (debug-iter?)
                       (-blm? A)
                       (= 0 (set-count (σₖ@ (-Σ-σₖ Σ) αₖ))))
              (hash-ref! print-cache A (λ () (printf "~a~n" (show-blm A))))))
          (match A
            [(-blm l+ _ _ _ _) #:when (symbol? l+) ; ignore blames on system
             ∅]
            [_
             (match-define (-Σ _ _ M) Σ)
             (define A*
               (match A
                 [(-W (list V) s) (-W (list (V+ (-Σ-σ Σ) V (predicates-of Γ s))) s)]
                 [_ A]))
             (unless (-ℋ𝒱? αₖ)
               (M⊕! Σ αₖ (-Γ-facts Γ) A*))
             (maybe-print-blame)
             {set (-ς↓ αₖ Γ A*)}])))
      (set-⟦k⟧->αₖ! ⟦k⟧ αₖ)
      (add-⟦k⟧-roots! ⟦k⟧ ∅eq)
      ⟦k⟧))

  (define-frame (ap∷ [Ws : (Listof -W¹)]
                     [⟦e⟧s : (Listof -⟦e⟧)]
                     [ρ : -ρ]
                     [ℒ : -ℒ]
                     [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define Ws* (cons (-W¹ V s) Ws))
         (match ⟦e⟧s
           ['()
            (match-define (cons Wₕ Wₓs) (reverse Ws*))
            (app $ ℒ Wₕ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ Ws* ⟦e⟧s* ρ ℒ ⟦k⟧))])]
        [_
         (define-values (ℓ l) (unpack-ℒ ℒ))
         (define blm
           (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs))) ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mon.c∷ [l³ : -l³]
                        [ℒ : -ℒ]
                        [C : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                        [⟦k⟧ : -⟦k⟧])
    (match-define (-l³ _ _ lo) l³)
    (define root (if (pair? C) (cdr C) C))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define W-V (-W¹ V s))
         (cond [(-W¹? C) (mon l³ $ ℒ C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦c⟧ ρ) C)
                (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℒ W-V ⟦k⟧))])]
        [else
         (define blm (-blm lo 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mon.v∷ [l³ : -l³]
                        [ℒ : -ℒ]
                        [V : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                        [⟦k⟧ : -⟦k⟧])
    (match-define (-l³ _ _ lo) l³)
    (define root (if (pair? V) (cdr V) V))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
      (match-define (-W Vs s) A)
      (match Vs
        [(list C)
         (define W-C (-W¹ C s))
         (cond [(-W¹? V) (mon l³ $ ℒ W-C V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦v⟧ ρ) V)
                (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.c∷ l³ ℒ W-C ⟦k⟧))])]
        [else
         (define blm (-blm lo 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  ;; let-values
  (define-frame (let∷ [ℓ : ℓ]
                      [xs : (Listof Symbol)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                      [bnd-Ws : (Listof (List Symbol -V -?t))]
                      [⟦e⟧ : -⟦e⟧]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs t) A)
      (define n (length xs))
      
      (cond
        [(= n (length Vs))
         (define bnd-Ws*
           (for/fold ([acc : (Listof (List Symbol -V -?t)) bnd-Ws])
                     ([x xs] [V Vs] [tₓ (split-values t n)])
             (cons (list x V tₓ) acc)))
         (match ⟦bnd⟧s
           ['()
            (match-define (-Σ σ _ _) Σ)
            (define-values (ρ* Γ*) ; with side effect widening store
              (for/fold ([ρ : -ρ ρ] [Γ : -Γ Γ])
                        ([bnd-W bnd-Ws*])
                (match-define (list (? symbol? x) (? -V? Vₓ) (? -?t? tₓ)) bnd-W)
                (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ (predicates-of-W (-Σ-σ Σ) Γ (-W¹ Vₓ tₓ)))))
                (σ⊕! Σ Γ α (-W¹ Vₓ tₓ))
                (values (ρ+ ρ x α) (-Γ-with-aliases Γ x tₓ))))
            (⟦e⟧ ρ* $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ $ Γ ⟪ℋ⟫ Σ (let∷ ℓ xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
        [else
         (define blm
           (-blm (ℓ-src ℓ) 'let-values
                 (list (format-symbol "requires ~a values" (length xs)))
                 (list (format-symbol "provided ~a values" (length Vs)))
                 +ℓ₀))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  ;; begin
  (define-frame (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
         (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (memoize-⟦k⟧ (bgn∷ ⟦e⟧s* ρ ⟦k⟧))))]))

  ;; begin0, waiting on first value
  (define-frame (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
         (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧)))]))

  ;; begin0, already have first value
  (define-frame (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['()
       (make-frame (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W)
         (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ))]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (make-frame (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W ρ)
         (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧)))]))

  ;; Conditional
  (define-frame (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V s)])
           #:true  (⟦e⟧₁ ρ $ Γ₁ ⟪ℋ⟫ Σ ⟦k⟧)
           #:false (⟦e⟧₂ ρ $ Γ₂ ⟪ℋ⟫ Σ ⟦k⟧))]
        [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs))) +ℓ₀) $ Γ ⟪ℋ⟫ Σ)])))

  ;; set!
  (define-frame (set!∷ [α : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs sᵥ) A)
      (match Vs
        [(list V)
         (σ⊕! Σ Γ α (-W¹ V sᵥ) #:mutating? #t)
         (define s
           (match (⟪α⟫->-α α)
             [(-α.x x _ _) (-x x)]
             [(? -𝒾? 𝒾) 𝒾]))
         (⟦k⟧ -void.W (hash-remove $ s) Γ ⟪ℋ⟫ Σ)]
        [_
         (define blm
           (-blm 'TODO 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs))) +ℓ₀))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  ;; letrec-values
  (define-frame (letrec∷ [ℓ : ℓ]
                         [xs : (Listof Symbol)]
                         [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                         [⟦e⟧ : -⟦e⟧]
                         [ρ : -ρ]
                         [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs s) A)
      (define n (length xs))
      (cond
        [(= n (length Vs))
         (match-define (-Σ σ _ _) Σ)
         (define Γ* ; with side effect widening store
           (for/fold ([Γ : -Γ Γ])
                     ([x xs] [Vₓ Vs] [sₓ (split-values s n)])
             (define α (ρ@ ρ x) #;(-α.x x #|TODO right?|# ⟪ℋ⟫))
             (σ⊕! Σ Γ α (-W¹ Vₓ sₓ))
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
  (define-frame (μ/c∷ [x : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W (list V) s) A)
      (define α (-α->⟪α⟫ (-α.x/c x)))
      (σ⊕V! Σ α V)
      (⟦k⟧ (-W (list (-x/C α)) s) $ Γ ⟪ℋ⟫ Σ)))

  ;; Non-dependent contract domain
  (define-frame (-->.dom∷ [Ws  : (Listof -W¹)]
                          [⟦c⟧s : (Listof -⟦e⟧)]
                          [⟦c⟧ᵣ : (Option -⟦e⟧)]
                          [⟦d⟧  : -⟦e⟧]
                          [ρ   : -ρ]
                          [ℓ   : ℓ]
                          [⟦k⟧  : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
      (match-define (-W (list V) s) A)
      (define Ws* (cons (-W¹ V s) Ws))
      (match ⟦c⟧s
        ['()
         (cond [⟦c⟧ᵣ (⟦c⟧ᵣ ρ $ Γ ⟪ℋ⟫ Σ (-->.rst∷ Ws* ⟦d⟧ ρ ℓ ⟦k⟧))]
               [else (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ Ws* #f ℓ ⟦k⟧))])]
        [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ Ws* ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧))])))

  ;; Non-depenent contract rest
  (define-frame (-->.rst∷ [Ws : (Listof -W¹)]
                          [⟦d⟧ : -⟦e⟧]
                          [ρ : -ρ]
                          [ℓ : ℓ]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
      (match-define (-W (list V) s) A)
      (define Wᵣ (-W¹ V s))
      (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ Ws Wᵣ ℓ ⟦k⟧))))

  ;; Non-dependent contract range
  (define-frame (-->.rng∷ [Ws : (Listof -W¹)]
                          [Wᵣ : (Option -W¹)]
                          [ℓₐ : ℓ]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws)
      (match-define (-W Ds d) A)
      (match Ds
        [(list D)
         (define β (-α->⟪α⟫ (-α.rng d ℓₐ #|TODO right?|# ⟪ℋ⟫)))
         (σ⊕V! Σ β D)
         (define-values (αs cs) ; with side effect widening store
           (for/fold ([αs : (Listof ⟪α⟫) '()]
                      [cs : (Listof -?t) '()])
                     ([(W i) (in-indexed Ws)] #:when (index? i))
             (match-define (-W¹ C c) W)
             (define α (-α->⟪α⟫ (-α.dom c ℓₐ ⟪ℋ⟫ i)))
             (σ⊕V! Σ α C)
             (values (cons α αs) (cons c cs))))
         (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
           (for/list ([(α i) (in-indexed αs)] #:when (index? i))
             (cons (cast α ⟪α⟫) (ℓ-with-id ℓₐ i))))
         (define βℓ (cons β (ℓ-with-id ℓₐ (length αs))))
         (define G
           (match Wᵣ
             [(-W¹ Vᵣ cᵣ)
              (define αᵣ (-α->⟪α⟫ (-α.rst cᵣ ℓₐ ⟪ℋ⟫)))
              (define ℓᵣ (ℓ-with-id ℓₐ 'rest))
              (σ⊕V! Σ αᵣ Vᵣ)
              (-W (list (-=> (-var αℓs (cons αᵣ ℓᵣ)) βℓ ℓₐ)) (-?-> (-var cs cᵣ) d))]
             [#f
              (-W (list (-=> αℓs βℓ ℓₐ)) (-?-> cs d))]))
         (⟦k⟧ G $ Γ ⟪ℋ⟫ Σ)]
        [_
         (error "TODO: `->`'s range for multiple values")])))

  ;; Given *reversed* list of contract domains and range-maker, create dependent contract
  (define (mk-=>i! [Σ : -Σ] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫]
                   [Ws : (Listof -W¹)] [Mk-D : -Clo] [mk-d : -λ] [ℓₐ : ℓ]) : (Values -V -?t)
    (define-values (αs cs) ; with side effect widening store
      (for/fold ([αs : (Listof ⟪α⟫) '()]
                 [cs : (Listof -?t) '()])
                ([(W i) (in-indexed Ws)])
        (match-define (-W¹ C c) W)
        (define α
          (-α->⟪α⟫ (-α.dom c ℓₐ ⟪ℋ⟫ (assert i exact-nonnegative-integer?))))
        (σ⊕V! Σ α C)
        (values (cons α αs) (cons c cs))))
    (define β (-α->⟪α⟫ (-α.rng mk-d ℓₐ ⟪ℋ⟫)))
    (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
      (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
        (cons (cast α ⟪α⟫) (ℓ-with-id ℓₐ i))))
    (define G (-=>i αℓs (list Mk-D mk-d (ℓ-with-id ℓₐ (length αs))) ℓₐ))
    (define g (-?->i cs mk-d))
    (σ⊕V! Σ β Mk-D)
    (values G g))

  ;; Dependent contract
  (define-frame (-->i∷ [Ws  : (Listof -W¹)]
                       [⟦c⟧s : (Listof -⟦e⟧)]
                       [ρ   : -ρ]
                       [Mk-D : -Clo]
                       [mk-d : -λ]
                       [ℓ    : ℓ]
                       [⟦k⟧  : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ Mk-D)
      (match-define (-W (list C) c) A)
      (define Ws* (cons (-W¹ C c) Ws))
      (match ⟦c⟧s
        ['()
         (define-values (G g) (mk-=>i! Σ Γ ⟪ℋ⟫ Ws* Mk-D mk-d ℓ))
         (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ)]
        [(cons ⟦c⟧ ⟦c⟧s*)
         (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

  ;; case-> contract
  (define-frame (case->∷ [ℓ : ℓ]
                         [Clauses : (Listof (Listof -W¹))]
                         [Cs : (Listof -W¹)]
                         [⟦c⟧s : (Listof -⟦e⟧)]
                         [⟦clause⟧s : (Listof (Listof -⟦e⟧))]
                         [ρ : -ρ]
                         [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
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
  (define-frame (struct/c∷ [ℓ₁ : ℓ]
                           [𝒾 : -𝒾]
                           [Cs : (Listof -W¹)]
                           [⟦c⟧s : (Listof -⟦e⟧)]
                           [ρ : -ρ]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (#;Cs ρ)
      (match-define (-W (list C) c) A)
      (define Cs* (cons (-W¹ C c) Cs))
      (match ⟦c⟧s
        ['()
         (define-values (αs cs flat?) ; with side effect widening store
           (for/fold ([αs : (Listof ⟪α⟫) '()]
                      [cs : (Listof -?t) '()]
                      [flat? : Boolean #t])
                     ([(W i) (in-indexed Cs*)])
             (match-define (-W¹ C c) W)
             (define α
               (-α->⟪α⟫ (-α.struct/c c 𝒾 ℓ₁ ⟪ℋ⟫ (assert i exact-nonnegative-integer?))))
             (σ⊕V! Σ α C)
             (values (cons α αs)
                     (cons c cs)
                     (and flat? (C-flat? C)))))
         (define αℓs : (Listof (Pairof ⟪α⟫ ℓ))
           (for/list ([(α i) (in-indexed αs)] #:when (exact-nonnegative-integer? i))
             (cons (cast α ⟪α⟫) (ℓ-with-id ℓ₁ i))))
         (define W (-W (list (-St/C flat? 𝒾 αℓs)) (apply ?t@ (-st/c.mk 𝒾) cs)))
         (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ)]
        [(cons ⟦c⟧ ⟦c⟧s*)
         (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (struct/c∷ ℓ₁ 𝒾 Cs* ⟦c⟧s* ρ ⟦k⟧))])))

  ;; define
  (define-frame (def∷ [l : -l]
                  [αs : (Listof ⟪α⟫)]
                  [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (define n (length αs))
      (match-define (-W Vs s) A)
      (cond
        [(= n (length Vs))
         (for ([α : ⟪α⟫ αs] [V Vs])
           (σ⊕V! Σ α V))
         (⟦k⟧ -void.W $ Γ ⟪ℋ⟫ Σ)]
        [else
         (define blm
           (-blm l 'define-values
                 (list (format-symbol "~a values" n))
                 (list (format-symbol "~a values" (length Vs)))
                 +ℓ₀))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  ;; provide with contract
  (define-frame (dec∷ [ℓ : ℓ]
                      [𝒾 : -𝒾]
                      [⟦k⟧ : -⟦k⟧])
    (define l (-𝒾-ctx 𝒾))
    (define l³ (-l³ l 'dummy- l))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W (list C) c) A)
      (match-define (-Σ σ _ _) Σ)
      (define W-C (-W¹ C c))
      (define Vs (σ@ σ (-α->⟪α⟫ 𝒾)))
      (for/union : (℘ -ς) ([V Vs])
                 (mon l³ $ (-ℒ (seteq ℓ) ℓ) W-C (-W¹ V 𝒾) Γ ⟪ℋ⟫ Σ
                      (def∷ l (list (-α->⟪α⟫ (-α.wrp 𝒾))) ⟦k⟧)))))

  (define/memoeq (hv∷ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs _) A)
      (for ([V (in-list Vs)])
        (add-leak! Σ V))
      {set (-ς↑ (-ℋ𝒱) ⊤Γ ⟪ℋ⟫)}))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helper frames
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-frame (mk-wrap-vect∷ [tᵥ : -?t]
                               [Vₚ : (U -Vector/C -Vectorof)]
                               [ℒ : -ℒ]
                               [l³ : -l³]
                               [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Vₚ)
      (match-define (-W (list Vᵥ) _) A) ; only used internally, shoule be safe
      (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.unvct ℒ ⟪ℋ⟫ (-l³-pos l³))))
      (σ⊕V! Σ ⟪α⟫ᵥ Vᵥ)
      (⟦k⟧ (-W (list (-Vector/guard Vₚ ⟪α⟫ᵥ l³)) tᵥ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (mon-or/c∷ [l³ : -l³]
                           [ℒ : -ℒ]
                           [Wₗ : -W¹]
                           [Wᵣ : -W¹]
                           [W-V : -W¹]
                           [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Wₗ Wᵣ W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (mon l³ $ ℒ Wᵣ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(list (-b #t) V)
       (match-define (-W¹ Cₗ _) Wₗ)
       (define v*
         (match s
           [(-t.@ 'values (list _ v)) v]
           [#f #f]))
       (⟦k⟧ (-W (list (V+ (-Σ-σ Σ) V Cₗ)) v*) $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (if.flat/c∷ [W-V : -W] [blm : -blm] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-V)
      (match-define (-W Vs v) A)
      (match Vs
        [(list V)
         (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
           #:true  (⟦k⟧ W-V $ Γ₁ ⟪ℋ⟫ Σ)
           #:false (⟦k⟧ blm $ Γ₂ ⟪ℋ⟫ Σ))]
        [_
         (match-define (-blm _ lo _ _ ℓ) blm)
         (⟦k⟧ (-blm lo 'Λ '(|1 value|) Vs ℓ) $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (wrap-st∷ [𝒾 : -𝒾]
                          [tᵥ : -?t]
                          [C : -St/C]
                          [ℒ : -ℒ]
                          [l³ : -l³]
                          [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (C)
    (match-define (-W (list V) _) A)  ; only used internally, should be safe
    (define ⟪α⟫ᵤ (-α->⟪α⟫ (-α.st 𝒾 ℒ ⟪ℋ⟫ (-l³-pos l³))))
    (σ⊕! Σ Γ ⟪α⟫ᵤ (-W¹ V tᵥ))
    (⟦k⟧ (-W (list (-St* C ⟪α⟫ᵤ l³)) tᵥ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (fc-and/c∷ [l : -l]
                           [ℒ : -ℒ]
                           [W-C₁ : -W¹]
                           [W-C₂ : -W¹]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f)) (⟦k⟧ -ff.W $ Γ ⟪ℋ⟫ Σ)]
        [(list (-b #t) V)
         (match-define (-t.@ 'values (list _ sᵥ)) s)
         (match-define (-W¹ C₁ _) W-C₁)
         (flat-chk l $ ℒ W-C₂ (-W¹ (V+ (-Σ-σ Σ) V C₁) sᵥ) Γ ⟪ℋ⟫ Σ ⟦k⟧)])))

  (define-frame (fc-or/c∷ [l : -l]
                          [ℒ : -ℒ]
                          [W-C₁ : -W¹]
                          [W-C₂ : -W¹]
                          [W-V : -W¹]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f))
         (flat-chk l $ ℒ W-C₂ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
        [(list (-b #t) V)
         (match-define (-W¹ C₁ _) W-C₁)
         (⟦k⟧ (-W (list -tt (V+ (-Σ-σ Σ) V C₁)) s) $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (fc-not/c∷ [l : -l]
                           [W-C* : -W¹]
                           [W-V : -W¹]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C* W-V)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f))
         (match-define (-W¹ V v) W-V)
         (⟦k⟧ (-W (list -tt V) (?t@ 'values -tt v)) $ Γ ⟪ℋ⟫ Σ)]
        [(list (-b #t) V)
         (⟦k⟧ -ff.W $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (fc-struct/c∷ [l : -l]
                              [ℒ : -ℒ]
                              [𝒾 : -𝒾]
                              [W-Vs-rev : (Listof -W¹)]
                              [⟦e⟧s : (Listof -⟦e⟧)]
                              [ρ : -ρ]
                              [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-Vs-rev ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f))
         (⟦k⟧ -ff.W $ Γ ⟪ℋ⟫ Σ)]
        [(list (-b #t) V*)
         (define v*
           (match s
             [(-t.@ 'values (list _ v)) v]
             [#f #f]))
         (match ⟦e⟧s
           ['()
            (define ⟦k⟧*
              (let ([k (-st-mk 𝒾)])
                (ap∷ (append W-Vs-rev (list (-W¹ k k))) '() ⊥ρ ℒ
                     (ap∷ (list (-W¹ -tt -tt) (-W¹ 'values 'values)) '() ⊥ρ ℒ ⟦k⟧))))
            (⟦k⟧* (-W (list V*) v*) $ Γ ⟪ℋ⟫ Σ)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (define W* (-W¹ V* v*))
            (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℒ 𝒾 (cons W* W-Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

  (define-frame (fc.v∷ [l : -l]
                       [ℒ : -ℒ]
                       [⟦v⟧ : -⟦e⟧]
                       [ρ : -ρ]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list C)
         (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.c∷ l ℒ (-W¹ C s) ⟦k⟧))]
        [_
         (define blm (-blm l 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (fc.c∷ [l : -l]
                       [ℒ : -ℒ]
                       [W-C : -W¹]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (flat-chk l $ ℒ W-C (-W¹ V s) Γ ⟪ℋ⟫ Σ ⟦k⟧)]
        [_
         (define blm (-blm l 'Λ '(|1 value|) Vs (-ℒ-app ℒ)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (and∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (if∷ l ⟦e⟧ ⟦ff⟧ ρ (and∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define-frame (or∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*) ; TODO propagate value instead
       (if∷ l ⟦tt⟧ ⟦e⟧ ρ (or∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define-frame (neg∷ [l : -l] [⟦k⟧ : -⟦k⟧]) (if∷ l ⟦ff⟧ ⟦tt⟧ ⊥ρ ⟦k⟧))

  (define-frame (mk-listof∷ [tₐ : -?t] [ℒ₀ : -ℒ] [⟪ℋ⟫₀ : -⟪ℋ⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define ⟪α⟫ₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ₀ ⟪ℋ⟫₀ 0)))
         (define ⟪α⟫ₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ₀ ⟪ℋ⟫₀ 1)))
         (define Vₚ (-Cons ⟪α⟫ₕ ⟪α⟫ₜ))
         (σ⊕V! Σ ⟪α⟫ₕ V)
         (σ⊕V! Σ ⟪α⟫ₜ -null)
         (σ⊕V! Σ ⟪α⟫ₜ Vₚ)
         (⟦k⟧ (-W (list Vₚ) tₐ) $ Γ ⟪ℋ⟫ Σ)]
        [_
         (define blm (blm-arity (-ℒ-app ℒ₀) 'mk-listof 1 Vs))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))
  )
