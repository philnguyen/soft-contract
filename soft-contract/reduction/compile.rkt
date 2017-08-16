#lang typed/racket/base

(provide compile@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit compile@
  (import kont^ widening^ memoize^ proof-system^ local-prover^
          env^ sto^ pc^ val^ pretty-print^ for-gc^)
  (export compile^)

  ;; Compile program
  (define (↓ₚ [ms : (Listof -module)] [e : -e]) : -⟦e⟧
    (define ⟦e⟧ (↓ₑ '† e))
    (match (map ↓ₘ ms)
      ['() ⟦e⟧]
      [(cons ⟦m⟧ ⟦m⟧s)
       (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
         (⟦m⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ `(,@⟦m⟧s ,⟦e⟧) ρ ⟦k⟧)))]))

  ;; Compile module
  (define (↓ₘ [m : -module]) : -⟦e⟧
    (match-define (-module l ds) m)

    (: ↓pc : -provide-spec → -⟦e⟧)
    (define ↓pc
      (match-lambda
        ;; Wrap contract
        [(-p/c-item x c ℓ)
         (define ⟦c⟧ (↓ₑ l c))
         (define 𝒾 (-𝒾 x l))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (dec∷ ℓ 𝒾 ⟦k⟧)))]
        ;; export same as internal
        [(? symbol? x)
         (define α (-α->⟪α⟫ (-𝒾 x l)))
         (define α* (-α->⟪α⟫ (-α.wrp (-𝒾 x l))))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (when (defined-at? Σ α)
             (for ([V (in-set (σ@ Σ α))])
               (σ⊕V! Σ α* V)))
           (⟦k⟧ (+W (list -void)) $ Γ ⟪ℋ⟫ Σ))]))
    
    (: ↓d : -module-level-form → -⟦e⟧)
    (define (↓d d)
      (match d
        [(-define-values xs e)
         (define αs : (Listof ⟪α⟫) (for/list ([x xs]) (-α->⟪α⟫ (-𝒾 x l))))
         (define ⟦e⟧ (↓ₑ l e))
         (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (def∷ l αs ⟦k⟧)))]
        [(-provide specs)
         (match (map ↓pc specs)
           ['() (↓ₚᵣₘ -void)]
           [(cons ⟦spec⟧ ⟦spec⟧s)
            (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
              (⟦spec⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦spec⟧s ρ ⟦k⟧)))])]
        [(? -e? e) (↓ₑ l e)]
        [_
         (log-warning "↓d : ignore ~a~n" (show-module-level-form d))
         (↓ₚᵣₘ -void)]))

    (match (map ↓d ds)
      ['() (↓ₚᵣₘ -void)]
      [(cons ⟦d⟧ ⟦d⟧s)
       (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
         (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦d⟧s ρ ⟦k⟧)))]))

  ;; Compile expression to computation
  (define (↓ₑ [l : -l] [e : -e]) : -⟦e⟧
    (let ↓ ([e : -e e])
      (remember-e!
       e
       (match e
         [(-λ xs e*)
          (define ⟦e*⟧ (memoize-⟦e⟧ (↓ e*)))
          (set-bound-vars! ⟦e*⟧ (bv e*))
          (define fvs (fv e*))
          #;(printf "Warning: no longer canonicalize λ-term~n")
          (define t (-λ xs e*))
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (define ρ* (m↓ ρ fvs))
            (define Γ*
              (for*/set: : -Γ ([φ (in-set Γ)]
                               [fv⟦φ⟧ (in-value (fvₜ φ))]
                               #:unless (set-empty? fv⟦φ⟧)
                               #:when (⊆ fv⟦φ⟧ fvs))
                φ))
            (⟦k⟧ (-W (list (-Clo xs ⟦e*⟧ ρ* Γ*)) t) $ Γ ⟪ℋ⟫ Σ))]
         [(-case-λ clauses)
          (define ⟦clause⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (for/list ([clause clauses])
              (match-define (cons xs e) clause)
              (cons xs (↓ e))))
          (define t (-case-λ clauses))
          #;(printf "Warning: no longer canonicalize λ-term~n")
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦k⟧ (-W (list (-Case-Clo ⟦clause⟧s ρ Γ)) t) $ Γ ⟪ℋ⟫ Σ))]
         [(? -prim? p) (↓ₚᵣₘ p)]
         [(-•)
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦k⟧ (-W (list (+●)) #f) $ Γ ⟪ℋ⟫ Σ))]
         [(-x x ℓₓ) (↓ₓ l x ℓₓ)]
         [(-ref (and 𝒾 (-𝒾 x l₀)) ℓᵣ)
          (define-values (α modify-V)
            (cond
              ;; same-module referencing returns unwrapped version
              [(equal? l₀ l)
               (values 𝒾 (inst values -V))]
              ;; cross-module referencing returns wrapped version
              ;; when the caller is symbolic (HACK)
              ;; and supplies the negative monitoring context (HACK)
              [(symbol? l)
               (values (-α.wrp 𝒾) (λ ([V : -V]) (with-negative-party l V)))]
              ;; cross-mldule referencing returns abstracted wrapped version
              ;; when the caller is concrete (HACK)
              ;; and supplies the negative monitoring context (HACK)
              [else
               (values (-α.wrp 𝒾) (λ ([V : -V])
                                    (with-positive-party 'dummy+
                                      (with-negative-party l
                                        (approximate-under-contract V)))))]))
          
          (define ⟪α⟫ (-α->⟪α⟫ α))
          (define ?loc (hack:α->loc ⟪α⟫))

          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (unless (hash-has-key? (-Σ-σ Σ) ⟪α⟫ₒₚ) ; HACK
              (σ⊕V! Σ ⟪α⟫ₒₚ (+●)))
            (cond
              [?loc
               (define-values (Ws $*) ($@! Σ Γ ⟪α⟫ $ ?loc ℓᵣ))
               (for/union : (℘ -ς) ([W (in-set Ws)])
                          (⟦k⟧ (W¹->W W) $* Γ ⟪ℋ⟫ Σ))]
              [else
               (for/union : (℘ -ς) ([V (in-set (σ@ Σ ⟪α⟫))])
                          (define V* (modify-V V))
                          (⟦k⟧ (-W (list V*) ℓᵣ) $ Γ ⟪ℋ⟫ Σ))]))]
         
         [(-@ f xs ℓ)
          (define ⟦f⟧  (↓ f))
          (define ⟦x⟧s (map ↓ xs))
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦f⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ '() ⟦x⟧s ρ ℓ ⟦k⟧)))]
         [(-if e₀ e₁ e₂)
          (define ⟦e₀⟧ (↓ e₀))
          (define ⟦e₁⟧ (↓ e₁))
          (define ⟦e₂⟧ (↓ e₂))
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦e₀⟧ ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
         [(-wcm k v b) (error '↓ₑ "TODO: wcm")]
         [(-begin es)
          (match (map ↓ es)
            ['()
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦k⟧ (+W (list -void)) $ Γ ⟪ℋ⟫ Σ))]
            [(cons ⟦e⟧ ⟦e⟧s)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s ρ ⟦k⟧)))])]
         [(-begin0 e₀ es)
          (define ⟦e₀⟧ (↓ e₀))
          (define ⟦e⟧s (map ↓ es))
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦e₀⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn0.v∷ ⟦e⟧s ρ ⟦k⟧)))]
         [(-quote q)
          (cond [(Base? q) (↓ₚᵣₘ (-b q))]
                [else (error '↓ₑ "TODO: (quote ~a)" q)])]
         [(-let-values bnds e* ℓ)
          (define ⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (for/list ([bnd bnds])
              (match-define (cons xs eₓₛ) bnd)
              (cons xs (↓ eₓₛ))))
          (define ⟦e*⟧ (↓ e*))
          (match ⟦bnd⟧s
            ['() ⟦e*⟧]
            [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
             (define bounds (append-map (inst car (Listof Symbol) -e) bnds))
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (define ⟦k⟧* (restore-$∷ ($-extract $ bounds) ⟦k⟧))
               (⟦e⟧ₓₛ ρ $ Γ ⟪ℋ⟫ Σ (let∷ ℓ xs ⟦bnd⟧s* '() ⟦e*⟧ ρ ⟦k⟧*)))])]
         [(-letrec-values bnds e* ℓ)
          (define ⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (for/list ([bnd bnds])
              (match-define (cons xs eₓₛ) bnd)
              (cons xs (↓ eₓₛ))))
          (define ⟦e*⟧ (↓ e*))
          (match ⟦bnd⟧s
            ['() ⟦e*⟧]
            [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
             (define bounds (append-map (inst car (Listof Symbol) -e) bnds))
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (define ρ* ; with side effect widening store
                 (for*/fold ([ρ  : -ρ  ρ])
                            ([⟦bnd⟧ ⟦bnd⟧s]
                             [xs (in-value (car ⟦bnd⟧))]
                             [x xs])
                   (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫)))
                   (σ⊕V! Σ α -undefined)
                   (ρ+ ρ x α)))
               (define ⟦k⟧* (restore-$∷ ($-extract $ bounds) ⟦k⟧))
               (⟦e⟧ₓₛ ρ* $ Γ ⟪ℋ⟫ Σ (letrec∷ ℓ xs ⟦bnd⟧s* ⟦e*⟧ ρ* ⟦k⟧*)))])]
         [(-set! x e*)
          (define ⟦e*⟧ (↓ e*))
          (cond
            [(symbol? x)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦e*⟧ ρ $ Γ ⟪ℋ⟫ Σ (set!∷ (ρ@ ρ x) ⟦k⟧)))]
            [else
             (define α (-α->⟪α⟫ x))
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦e*⟧ ρ $ Γ ⟪ℋ⟫ Σ (set!∷ α ⟦k⟧)))])]
         [(-error msg ℓ)
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦k⟧ (-blm (ℓ-src ℓ) 'Λ '() (list (-b msg)) ℓ) $ Γ ⟪ℋ⟫ Σ))]
         [(-μ/c x c)
          (define ⟦c⟧ (↓ c))
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (μ/c∷ x ⟦k⟧)))]
         [(--> cs d ℓ)
          (define ⟦d⟧ (↓ d))
          (match (-var-map ↓ cs)
            ['()
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦d⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.rng∷ '() #f ℓ ⟦k⟧)))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ '() ⟦c⟧s #f ⟦d⟧ ρ ℓ ⟦k⟧)))]
            [(-var ⟦c⟧s ⟦c⟧ᵣ)
             (match ⟦c⟧s
               ['()
                (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
                  (⟦c⟧ᵣ ρ $ Γ ⟪ℋ⟫ Σ (-->.rst∷ '() ⟦d⟧ ρ ℓ ⟦k⟧)))]
               [(cons ⟦c⟧ ⟦c⟧s*)
                (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
                  (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->.dom∷ '() ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧)))])])]
         [(-->i cs (and mk-d (-λ xs d)) ℓ)
          (define ⟦d⟧ (↓ d))
          (match (map ↓ cs)
            ['()
             (define c (-?->i '() mk-d))
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
               (define-values (G g) (mk-=>i! Σ Γ ⟪ℋ⟫ '() Mk-D mk-d ℓ))
               (⟦k⟧ (-W (list G) g) $ Γ ⟪ℋ⟫ Σ))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
               (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (-->i∷ '() ⟦c⟧s ρ Mk-D mk-d ℓ ⟦k⟧)))])]
         [(-case-> clauses ℓ)
          (define ⟦clause⟧s : (Listof (Listof -⟦e⟧))
            (for/list ([clause clauses])
              (match-define (cons cs d) clause)
              `(,@(map ↓ cs) ,(↓ d))))
          (match ⟦clause⟧s
            ['()
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦k⟧ (-W (list (-Case-> '() ℓ)) #f) $ Γ ⟪ℋ⟫ Σ))]
            [(cons (cons ⟦c⟧ ⟦c⟧s) ⟦clause⟧s*)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (case->∷ ℓ '() '() ⟦c⟧s ⟦clause⟧s* ρ ⟦k⟧)))])]
         [(-x/c x)
          (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            (⟦k⟧ (-W (list (-x/C (-α->⟪α⟫ (-α.x/c x)))) #f) $ Γ ⟪ℋ⟫ Σ))]
         [(-struct/c 𝒾 cs ℓ)
          (define α (-α->⟪α⟫ 𝒾))
          (define blm (-blm l 'Λ '(struct-defined?) (list (-𝒾-name 𝒾)) ℓ))
          (define builtin-struct-tag? (match? 𝒾 (== -𝒾-cons) (== -𝒾-box)))
          (match (map ↓ cs)
            ['()
             (define W (-W (list (-St/C #t 𝒾 '())) (-t.@ (-st/c.mk 𝒾) '())))
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (define A (if (or builtin-struct-tag? (defined-at? Σ α)) W blm))
               (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
               (if (or builtin-struct-tag? (defined-at? Σ α))
                   (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (struct/c∷ ℓ 𝒾 '() ⟦c⟧s ρ ⟦k⟧))
                   (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)))])]
         [_ (error '↓ₑ "unhandled: ~a" (show-e e))])))

    )

  (define/memo (↓ₓ [l : -l] [x : Symbol] [ℓₓ : ℓ]) : -⟦e⟧
    (define -blm.undefined
      (-blm l 'Λ (list 'defined?) (list (format-symbol "~a_(~a)" 'undefined x)) ℓₓ))
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (define α (ρ@ ρ x))
      (define-values (Ws $*) ($@! Σ Γ α $ x ℓₓ))
      (for/union : (℘ -ς) ([W (in-set Ws)])
        (define A
          (match W
            [(-W¹ (-b (== undefined)) _) -blm.undefined]
            [(-W¹ V                   t) (-W (list V) t)]))
        (⟦k⟧ A $* Γ ⟪ℋ⟫ Σ))))

  (define (↓ₚᵣₘ [p : -prim]) (ret-W¹ p p))

  (define/memo (ret-W¹ [V : -V] [t : -?t]) : -⟦e⟧
    (define W (-W (list V) t))
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ)))

  (define/memo (mk-mon [l³ : -l³] [ℓ : ℓ] [⟦c⟧ : -⟦e⟧] [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℓ (cons ⟦e⟧ ρ) ⟦k⟧))))

  (define/memo (mk-app [ℓ : ℓ] [⟦f⟧ : -⟦e⟧] [⟦x⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (⟦f⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ '() ⟦x⟧s ρ ℓ ⟦k⟧))))

  (define/memo (mk-rt [A : (U -A -W¹)]) : -⟦e⟧
    (match A
      [(-W¹ V v) (mk-rt (-W (list V) v))]
      [(? -A?) (λ (_ $ Γ ⟪ℋ⟫ Σ ⟦k⟧) (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))]))

  (define/memo (mk-fc [l : -l] [ℓ : ℓ] [⟦c⟧ : -⟦e⟧] [⟦v⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.v∷ l ℓ ⟦v⟧ ρ ⟦k⟧))))

  (define/memo (mk-wrapped-hash [C : -Hash/C] [l³ : -l³] [α : ⟪α⟫] [W : -W¹]) : -⟦e⟧
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match-define (-W¹ V t) W)
      (σ⊕V! Σ α V)
      (⟦k⟧ (-W (list (-Hash/guard C α l³)) t) $ Γ ⟪ℋ⟫ Σ)))
  )

