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
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide kont@)

(define-unit kont@
  (import compile^ app^ mon^ proof-system^ widening^ memoize^ for-gc^ verifier^
          val^ env^ sto^ pretty-print^ pc^ instr^)
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
              (hash-ref! print-cache A (λ () (printf "~a~n" (show-A A))))))
          (match A
            [(-blm l+ _ _ _ _) #:when (symbol? l+) ; ignore blames on system
             ∅]
            [_
             (define A*
               (match A
                 [(-W (list V) s) (-W (list (V+ (-Σ-σ Σ) V (predicates-of Γ s))) s)]
                 [_ A]))
             ;; TODO only need to save results for top-most block in "production" mode
             (M⊕! Σ αₖ (-ΓA Γ A*))
             (maybe-print-blame)
             {set (-ς↓ αₖ ($-cleanup $) Γ A*)}])))
      (set-⟦k⟧->αₖ! ⟦k⟧ αₖ)
      (add-⟦k⟧-roots! ⟦k⟧ ∅eq)
      ⟦k⟧))

  (define-frame (ap∷ [Ws : (Listof -W¹)]
                     [⟦e⟧s : (Listof -⟦e⟧)]
                     [ρ : -ρ]
                     [ℓ : ℓ]
                     [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define Ws* (cons (-W¹ V s) Ws))
         (match ⟦e⟧s
           ['()
            (match-define (cons Wₕ Wₓs) (reverse Ws*))
            (app ℓ Wₕ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ Ws* ⟦e⟧s* ρ ℓ ⟦k⟧))])]
        [_
         (define l (ℓ-src ℓ))
         (define blm
           (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs))) ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mon.c∷ [ctx : -ctx] [C : (U (Pairof -⟦e⟧ -ρ) -W¹)] [⟦k⟧ : -⟦k⟧])
    (match-define (-ctx _ _ lo ℓ) ctx)
    (define root (if (pair? C) (cdr C) C))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define W-V (-W¹ V s))
         (cond [(-W¹? C) (push-mon ctx C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦c⟧ ρ) C)
                (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ ctx W-V ⟦k⟧))])]
        [else
         (define blm (-blm lo 'Λ '(|1 value|) Vs ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mon.v∷ [ctx : -ctx] [V : (U (Pairof -⟦e⟧ -ρ) -W¹)] [⟦k⟧ : -⟦k⟧])
    (match-define (-ctx _ _ lo ℓ) ctx)
    (define root (if (pair? V) (cdr V) V))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
      (match-define (-W Vs s) A)
      (match Vs
        [(list C)
         (define W-C (-W¹ C s))
         (cond [(-W¹? V) (push-mon ctx W-C V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
               [else
                (match-define (cons ⟦v⟧ ρ) V)
                (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.c∷ ctx W-C ⟦k⟧))])]
        [else
         (define blm (-blm lo 'Λ '(|1 value|) Vs ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mon*.c∷ [ctx : -ctx] [rngs : (U (Listof -⟪α⟫ℓ) 'any)] [d : -?t] [⟦k⟧ : -⟦k⟧])
    (case rngs
      [(any) ⟦k⟧]
      [else
       (define-values (βs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc rngs))
       (define n (length rngs))
       (match-define (-ctx l+ _ lo ℓ) ctx)
       (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (βs)
         (match-define (-W Vs v) A)
         (cond
           [(= n (length Vs))
            (define vs (split-values v n))
            (define ds (split-values d n))
            (define Vals (map -W¹ Vs vs))
            (for/union : (℘ -ς) ([Ds (in-set (σ@/list Σ βs))])
              (define Ctcs (map -W¹ Ds ds))
              (match* (Ctcs Vals ℓs)
                [((cons Ctc₁ Ctcs*) (cons Val₁ Vals*) (cons ℓ₁ ℓs*))
                 (push-mon (ctx-with-ℓ ctx ℓ₁) Ctc₁ Val₁ $ Γ ⟪ℋ⟫ Σ
                           (mon*∷ ctx Ctcs* Vals* ℓs* '() ⟦k⟧))]
                [('() '() '())
                 (⟦k⟧ (+W '()) $ Γ ⟪ℋ⟫ Σ)]))]
           [else
            (define msg
              (format-symbol (case n
                               [(0 1) "~a value"]
                               [else "~a values"])
                             n))
            (define blm (-blm l+ lo (list msg) Vs ℓ))
            (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))]))

  (define-frame (mon*∷ [ctx : -ctx]
                       [W-Cs : (Listof -W¹)]
                       [W-Vs : (Listof -W¹)]
                       [ℓs : (Listof ℓ)]
                       [res.rev : (Listof -W¹)]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-Cs W-Vs)
      (match-define (-W (list V) t) A)
      (define res.rev* (cons (-W¹ V t) res.rev))
      (match* (W-Cs W-Vs ℓs)
        [((cons W-C₁ W-Cs*) (cons W-V₁ W-Vs*) (cons ℓ₁ ℓs*))
         (push-mon (ctx-with-ℓ ctx ℓ₁) W-C₁ W-V₁ $ Γ ⟪ℋ⟫ Σ
                   (mon*∷ ctx W-Cs* W-Vs* ℓs* res.rev* ⟦k⟧))]
        [('() '() '())
         (define-values (Vsₐ tsₐ) (unzip-by -W¹-V -W¹-t (reverse res.rev*)))
         (define Wₐ (-W Vsₐ (apply ?t@ 'values tsₐ)))
         (⟦k⟧ Wₐ $ Γ ⟪ℋ⟫ Σ)])))

  ;; let-values
  (define-frame (let∷ [ℓ : ℓ]
                      [xs : (Listof Symbol)]
                      [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                      [bnd-Ws : (Listof (Pairof Symbol -W¹))]
                      [⟦e⟧ : -⟦e⟧]
                      [ρ : -ρ]
                      [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs t) A)
      (define n (length xs))
      
      (cond
        [(= n (length Vs))
         (define bnd-Ws*
           (for/fold ([acc : (Listof (Pairof Symbol -W¹)) bnd-Ws])
                     ([x xs] [V Vs] [tₓ (split-values t n)])
             (cons (cons x (-W¹ V tₓ)) acc)))
         (match ⟦bnd⟧s
           ['()
            (define-values (ρ* $*)
              (let-values ([(xs Ws) (unzip bnd-Ws*)])
                (bind-args! Σ $ Γ ρ ⟪ℋ⟫ xs Ws #f)))
            #;(when (and (hash-has-key? ρ* 'l) (not (hash-has-key? $* 'l)))
              (printf "executing ~a, direct args ~a, with cache:~n" (show-⟦e⟧ ⟦e⟧) xs)
              (for ([(l W) (in-hash $)])
                (printf "- ~a ↦ ~a~n" (show-loc l) (show-W¹ W))))
            (⟦e⟧ ρ* $* Γ ⟪ℋ⟫ Σ ⟦k⟧)]
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
         (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

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
         (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V Γ V s)])
           #:true  (⟦e⟧₁ ρ $ Γ₁ ⟪ℋ⟫ Σ ⟦k⟧)
           #:false (⟦e⟧₂ ρ $ Γ₂ ⟪ℋ⟫ Σ ⟦k⟧))]
        [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs))) +ℓ₀) $ Γ ⟪ℋ⟫ Σ)])))

  ;; set!
  (define-frame (set!∷ [α : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (define ?loc (hack:α->loc α))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs sᵥ) A)
      (match Vs
        [(list V)
         (σ⊕! Σ Γ α (-W¹ V sᵥ))
         (define $* (if ?loc ($-set $ ?loc sᵥ) $))
         (⟦k⟧ (+W (list -void)) $* Γ ⟪ℋ⟫ Σ)]
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
         (define-values (ρ* $*)
           (let ([Wₓs (map -W¹ Vs (split-values s n))])
             (bind-args! Σ $ Γ ρ ⟪ℋ⟫ xs Wₓs #f)))
         (assert (equal? ρ ρ*)) ; FIXME disable in production
         (for ([x (in-list xs)])
           (σ-remove! Σ (hash-ref ρ x) -undefined))
         (match ⟦bnd⟧s
           ['()
            (⟦e⟧ ρ $* Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
            (⟦e⟧* ρ $* Γ ⟪ℋ⟫ Σ (letrec∷ ℓ xs* ⟦bnd⟧s* ⟦e⟧ ρ ⟦k⟧))])]
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
         (cond [⟦c⟧ᵣ  (⟦c⟧ᵣ (flip-seals ρ) $ Γ ⟪ℋ⟫ Σ (-->.rst∷ Ws* ⟦d⟧ ρ ℓ ⟦k⟧))]
               [else (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ Ws* #f ℓ ⟦k⟧))])]
        [(cons ⟦c⟧ ⟦c⟧s*) (⟦c⟧ (flip-seals ρ) $ Γ ⟪ℋ⟫ Σ (-->.dom∷ Ws* ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧))])))

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
                          [ℓ : ℓ]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws)
      (define-values (G g) (mk-=>! Σ Γ ⟪ℋ⟫ Ws Wᵣ A ℓ))
      (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ)
      #;(match Ds
        [(list D)
         (define G
           (match Wᵣ
             [(-W¹ Vᵣ cᵣ)
              (define αᵣ (-α->⟪α⟫ (-α.rst cᵣ ℓₐ ⟪ℋ⟫)))
              (define ℓᵣ (ℓ-with-id ℓₐ 'rest))
              (σ⊕V! Σ αᵣ Vᵣ)
              (-W (list (-=> (-var αℓs (cons αᵣ ℓᵣ)) βℓ ℓₐ)) (-?-> (-var cs cᵣ) d))]
             [#f
              (-W (list (-=> αℓs βℓ ℓₐ)) (-?-> cs d))]))
         (⟦k⟧ G Γ ⟪ℋ⟫ Σ)]
        [_
         (error "TODO: `->`'s range for multiple values")])))

  (: mk-=>! : -Σ -Γ -⟪ℋ⟫ (Listof -W¹) (Option -W¹) -W ℓ → (Values -V -?t))
  (define (mk-=>! Σ Γ ⟪ℋ⟫ doms.rev rst rngs ℓ)
    (match-define (-W Ds ds) rngs)
    (define-values (αs cs) ; with side-effect allocating domains
      (for/fold ([αs : (Listof ⟪α⟫) '()]
                 [cs : (Listof -?t) '()])
                ([W (in-list doms.rev)]
                 [i : Natural (in-naturals)])
        (match-define (-W¹ C c) W)
        (define α (-α->⟪α⟫ (-α.dom ℓ ⟪ℋ⟫ i)))
        (σ⊕V! Σ α C)
        (values (cons α αs) (cons c cs))))
    (define αℓs : (Listof -⟪α⟫ℓ)
      (for/list ([α : ⟪α⟫ (in-list αs)] [i : Natural (in-naturals)])
        (-⟪α⟫ℓ α (ℓ-with-id ℓ (cons 'dom i)))))
    (define Rng
      (match Ds
        ['(any) 'any]
        [_
         ;; With side-effect allocation range(s)
         (for/list : (Listof -⟪α⟫ℓ) ([D (in-list Ds)]
                                     [d (in-list (split-values ds (length Ds)))]
                                     [i : Natural (in-naturals)])
           (define β (-α->⟪α⟫ (-α.rng ℓ ⟪ℋ⟫ i)))
           (σ⊕V! Σ β D)
           (-⟪α⟫ℓ β (ℓ-with-id ℓ (cons 'rng i))))]))
    (define-values (Dom t-dom)
      (match rst
        [(-W¹ Vᵣ cᵣ)
         (define αᵣ (-α->⟪α⟫ (-α.rst ℓ ⟪ℋ⟫)))
         (define ℓᵣ (ℓ-with-id ℓ 'rest))
         (σ⊕V! Σ αᵣ Vᵣ)
         (values (-var αℓs (-⟪α⟫ℓ αᵣ ℓᵣ)) (-var cs cᵣ))]
        [_ (values αℓs cs)]))
    (values (-=> Dom Rng ℓ) (-?-> t-dom ds)))

  ;; Given *reversed* list of contract domains and range-maker, create dependent contract
  (: mk-=>i! : -Σ -Γ -⟪ℋ⟫ (Listof -W¹) -Clo -λ ℓ → (Values -V -?t))
  (define (mk-=>i! Σ Γ ⟪ℋ⟫ Ws Mk-D mk-d ℓₐ)
    (define-values (αs cs) ; with side effect widening store
      (for/fold ([αs : (Listof ⟪α⟫) '()]
                 [cs : (Listof -?t) '()])
                ([(W i) (in-indexed Ws)])
        (match-define (-W¹ C c) W)
        (define α
          (-α->⟪α⟫ (-α.dom ℓₐ ⟪ℋ⟫ (assert i exact-nonnegative-integer?))))
        (σ⊕V! Σ α C)
        (values (cons α αs) (cons c cs))))
    (define β (-α->⟪α⟫ (-α.rng ℓₐ ⟪ℋ⟫ #|TODO|# 0)))
    (define αℓs : (Listof -⟪α⟫ℓ)
      (for/list ([α : ⟪α⟫ (in-list αs)] [i : Natural (in-naturals)])
        (-⟪α⟫ℓ α (ℓ-with-id ℓₐ i))))
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
         (⟦c⟧ (flip-seals ρ) $ Γ ⟪ℋ⟫ Σ (-->i∷ Ws* ⟦c⟧s* ρ Mk-D mk-d ℓ ⟦k⟧))])))

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
               (-α->⟪α⟫ (-α.struct/c 𝒾 ℓ₁ ⟪ℋ⟫ (assert i exact-nonnegative-integer?))))
             (σ⊕V! Σ α C)
             (values (cons α αs)
                     (cons c cs)
                     (and flat? (C-flat? C)))))
         (define αℓs : (Listof -⟪α⟫ℓ)
           (for/list ([α : ⟪α⟫ (in-list αs)] [i : Natural (in-naturals)])
             (-⟪α⟫ℓ α (ℓ-with-id ℓ₁ i))))
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
         (define $*
           (for/fold ([$ : -$ $])
                     ([α : ⟪α⟫ (in-list αs)]
                      [V (in-list Vs)]
                      [t (in-list (split-values s n))])
             (σ⊕V! Σ α V)
             (define ?l (hack:α->loc α))
             (if ?l ($-set $ ?l t) $)))
         (⟦k⟧ (+W (list -void)) $* Γ ⟪ℋ⟫ Σ)]
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
    (define l (-𝒾-src 𝒾))
    (define ctx (-ctx l 'dummy- l ℓ))
    (define α (-α->⟪α⟫ 𝒾))
    (define α* (-α->⟪α⟫ (-α.wrp 𝒾)))
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (α)
      (match-define (-W (list C) c) A)
      (define W-C (-W¹ C c))
      (define Vs (σ@ Σ α))
      (define ⟦k⟧* (def∷ l (list α*) ⟦k⟧))
      (for/union : (℘ -ς) ([V Vs])
        (push-mon ctx W-C (-W¹ V 𝒾) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))))

  (define/memoeq (hv∷ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs _) A)
      (for ([V (in-list Vs)])
        (add-leak! Σ V))
      (define αₖ (-ℋ𝒱 $ ⟪ℋ⟫))
      (σₖ⊕! Σ αₖ (-κ ⟦k⟧))
      {set (-ς↑ αₖ)}))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helper frames
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-frame (mk-wrap-vect∷ [tᵥ : -?t]
                               [Vₚ : (U -Vector/C -Vectorof)]
                               [ctx : -ctx]
                               [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Vₚ)
      (match-define (-W (list Vᵥ) _) A) ; only used internally, shoule be safe
      (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.unvct ctx ⟪ℋ⟫)))
      (σ⊕V! Σ ⟪α⟫ᵥ Vᵥ)
      (⟦k⟧ (-W (list (-Vector/guard Vₚ ⟪α⟫ᵥ ctx)) tᵥ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (mon-or/c∷ [ctx : -ctx] [Wₗ : -W¹] [Wᵣ : -W¹] [W-V : -W¹] [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Wₗ Wᵣ W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (push-mon ctx Wᵣ W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
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
         (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V Γ V v)])
           #:true  (⟦k⟧ W-V $ Γ₁ ⟪ℋ⟫ Σ)
           #:false (⟦k⟧ blm $ Γ₂ ⟪ℋ⟫ Σ))]
        [_
         (match-define (-blm _ lo _ _ ℓ) blm)
         (⟦k⟧ (-blm lo 'Λ '(|1 value|) Vs ℓ) $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (wrap-st∷ [𝒾 : -𝒾]
                          [tᵥ : -?t]
                          [C : -St/C]
                          [ctx : -ctx]
                          [⟦k⟧ : -⟦k⟧])
  (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (C)
    (match-define (-W (list V) _) A)  ; only used internally, should be safe
    (define ⟪α⟫ᵤ (-α->⟪α⟫ (-α.st 𝒾 ctx ⟪ℋ⟫)))
    (σ⊕! Σ Γ ⟪α⟫ᵤ (-W¹ V tᵥ))
    (⟦k⟧ (-W (list (-St* C ⟪α⟫ᵤ ctx)) tᵥ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (fc-and/c∷ [l : -l]
                           [ℓ : ℓ]
                           [W-C₁ : -W¹]
                           [W-C₂ : -W¹]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f)) (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ)]
        [(list (-b #t) V)
         (match-define (-t.@ 'values (list _ sᵥ)) s)
         (match-define (-W¹ C₁ _) W-C₁)
         (push-fc l ℓ W-C₂ (-W¹ (V+ (-Σ-σ Σ) V C₁) sᵥ) $ Γ ⟪ℋ⟫ Σ ⟦k⟧)])))

  (define-frame (fc-or/c∷ [l : -l]
                          [ℓ : ℓ]
                          [W-C₁ : -W¹]
                          [W-C₂ : -W¹]
                          [W-V : -W¹]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f))
         (push-fc l ℓ W-C₂ W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
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
         (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (fc-struct/c∷ [l : -l]
                              [ℓ : ℓ]
                              [𝒾 : -𝒾]
                              [W-Vs-rev : (Listof -W¹)]
                              [⟦e⟧s : (Listof -⟦e⟧)]
                              [ρ : -ρ]
                              [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-Vs-rev ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list (-b #f))
         (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ)]
        [(list (-b #t) V*)
         (define v*
           (match s
             [(-t.@ 'values (list _ v)) v]
             [#f #f]))
         (match ⟦e⟧s
           ['()
            (define ⟦k⟧*
              (let ([k (-st-mk 𝒾)])
                (ap∷ (append W-Vs-rev (list (-W¹ k k))) '() ⊥ρ ℓ
                     (ap∷ (list (-W¹ -tt -tt) (-W¹ 'values 'values)) '() ⊥ρ ℓ ⟦k⟧))))
            (⟦k⟧* (-W (list V*) v*) $ Γ ⟪ℋ⟫ Σ)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (define W* (-W¹ V* v*))
            (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℓ 𝒾 (cons W* W-Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

  (define-frame (fc.v∷ [l : -l]
                       [ℓ : ℓ]
                       [⟦v⟧ : -⟦e⟧]
                       [ρ : -ρ]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
      (match-define (-W Vs s) A)
      (match Vs
        [(list C)
         (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.c∷ l ℓ (-W¹ C s) ⟦k⟧))]
        [_
         (define blm (-blm l 'Λ '(|1 value|) Vs ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (fc.c∷ [l : -l]
                       [ℓ : ℓ]
                       [W-C : -W¹]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C)
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (push-fc l ℓ W-C (-W¹ V s) $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
        [_
         (define blm (-blm l 'Λ '(|1 value|) Vs ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (and∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*)
       (if∷ l ⟦e⟧ (↓ₚᵣₘ -ff) ρ (and∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define-frame (or∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧])
    (match ⟦e⟧s
      ['() ⟦k⟧]
      [(cons ⟦e⟧ ⟦e⟧s*) ; TODO propagate value instead
       (if∷ l (↓ₚᵣₘ -tt) ⟦e⟧ ρ (or∷ l ⟦e⟧s* ρ ⟦k⟧))]))

  (define-frame (mk-listof∷ [tₐ : -?t] [ℓ₀ : ℓ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W Vs s) A)
      (match Vs
        [(list V)
         (define ⟪α⟫ₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℓ₀ ⟪ℋ⟫ 0)))
         (define ⟪α⟫ₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℓ₀ ⟪ℋ⟫ 1)))
         (define Vₚ (-Cons ⟪α⟫ₕ ⟪α⟫ₜ))
         (σ⊕V! Σ ⟪α⟫ₕ V)
         (σ⊕V! Σ ⟪α⟫ₜ -null)
         (σ⊕V! Σ ⟪α⟫ₜ Vₚ)
         (⟦k⟧ (-W (list Vₚ) tₐ) $ Γ ⟪ℋ⟫ Σ)]
        [_
         (define blm (blm-arity ℓ₀ 'mk-listof 1 Vs))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define-frame (mk-vector^∷ [Vₙ : -V] [tₐ : -?t] [ℓ : ℓ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (match-define (-W (list Vₑ) tₑ) A)
      (define α (-α->⟪α⟫ (-α.vct ℓ ⟪ℋ⟫)))
      (σ⊕! Σ Γ α (-W¹ Vₑ tₑ))
      (⟦k⟧ (-W (list (-Vector^ α Vₙ)) tₐ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (invalidate-$∷ [ls : (℘ -loc)] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (⟦k⟧ A ($-del* $ ls) Γ ⟪ℋ⟫ Σ)))

  (define-frame (restore-$∷ [δ$ : -δ$] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
      (⟦k⟧ A ($-restore $ δ$) Γ ⟪ℋ⟫ Σ)))

  (define-frame (restore-ctx∷ [⟪ℋ⟫ : -⟪ℋ⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ _ Σ) #:roots ()
      (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (hash-set-inner∷ [ℓ : ℓ] [αₕ : ⟪α⟫] [tₕ : -?t] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (αₕ)
      (match-define (-W (list Vₖ Vᵥ) tₐ) A)
      (match-define (list tₖ tᵥ) (split-values tₐ 2))
      (define Wₖ (-W¹ Vₖ tₖ))
      (define Wᵥ (-W¹ Vᵥ tᵥ))
      (for/union : (℘ -ς) ([Vₕ (in-set (σ@ Σ αₕ))])
        (app (ℓ-with-src ℓ 'hash-set-inner∷)
             (-W¹ 'hash-set 'hash-set)
             (list (-W¹ Vₕ tₕ) Wₖ Wᵥ)
             $ Γ ⟪ℋ⟫ Σ ⟦k⟧))))

  (define-frame (wrap-hash∷ [C : -Hash/C] [ctx : -ctx] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (C)
      (match-define (-W (list Vₕ) tₕ) A)
      (define α (-α->⟪α⟫ (-α.unhsh ctx ⟪ℋ⟫)))
      (σ⊕V! Σ α Vₕ)
      (define Vₐ (-Hash/guard C α ctx))
      (⟦k⟧ (-W (list Vₐ) tₕ) $ Γ ⟪ℋ⟫ Σ)))

  (define-frame (set-add-inner∷ [ℓ : ℓ] [αₛ : ⟪α⟫] [tₛ : -?t] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (αₛ)
      (match-define (-W¹ (list Vₑ) tₑ) A)
      (define Wₑ (-W¹ Vₑ tₑ))
      (for/union : (℘ -ς) ([Vₛ (in-set (σ@ Σ αₛ))])
        (app (ℓ-with-src ℓ 'set-add-inner∷)
             (-W¹ 'set-add 'set-add)
             (list (-W¹ Vₛ tₛ) Wₑ)
             $ Γ ⟪ℋ⟫ Σ ⟦k⟧))))

  (define-frame (wrap-set∷ [C : -Set/C] [ctx : -ctx] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (C)
      (match-define (-W (list Vₛ) tₛ) A)
      (define α (-α->⟪α⟫ (-α.unset ctx ⟪ℋ⟫)))
      (σ⊕V! Σ α Vₛ)
      (define Vₐ (-Set/guard C α ctx))
      (⟦k⟧ (-W (list Vₐ) tₛ) $ Γ ⟪ℋ⟫ Σ)))
  )
