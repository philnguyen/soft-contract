#lang typed/racket/base

(provide compile@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit compile@
  (import meta-functions^ ast-pretty-print^
          kont^ widening^ memoize^ proof-system^ local-prover^
          env^ sto^ pc^ val^ pretty-print^ for-gc^)
  (export compile^)

  (define ⟦e⟧-locs : (Mutable-HashTable -⟦e⟧ (℘ ℓ)) (make-hasheq))
  (define (loc-from-expr? [ℓ : ℓ] [⟦e⟧ : -⟦e⟧]) (map-has? ⟦e⟧-locs ⟦e⟧ ℓ))

  ;; Compile program
  (define (↓ₚ [ms : (Listof -module)] [e : -e]) : -⟦e⟧
    (define ⟦e⟧ (↓ₑ '† e))
    (match (map ↓ₘ ms)
      ['() ⟦e⟧]
      [(cons ⟦m⟧ ⟦m⟧s)
       (λ (ρ $ Γ H Σ ⟦k⟧)
         (⟦m⟧ ρ $ Γ H Σ (bgn∷ `(,@⟦m⟧s ,⟦e⟧) ρ ⟦k⟧)))]))

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
         (λ (ρ $ Γ H Σ ⟦k⟧)
           (⟦c⟧ ρ $ Γ H Σ (dec∷ ℓ 𝒾 ⟦k⟧)))]
        ;; export same as internal
        [(? symbol? x)
         (define α (-α->⟪α⟫ (-𝒾 x l)))
         (define α* (-α->⟪α⟫ (-α.wrp (-𝒾 x l))))
         (λ (ρ $ Γ H Σ ⟦k⟧)
           (assert (defined-at? Σ α))
           (σ-copy! Σ α α*)
           (⟦k⟧ (+W (list -void)) $ Γ H Σ))]))
    
    (: ↓d : -module-level-form → -⟦e⟧)
    (define (↓d d)
      (match d
        [(-define-values xs e)
         (define αs : (Listof ⟪α⟫) (for/list ([x xs]) (-α->⟪α⟫ (-𝒾 x l))))
         (define ⟦e⟧ (↓ₑ l e))
         (λ (ρ $ Γ H Σ ⟦k⟧)
           (⟦e⟧ ρ $ Γ H Σ (def∷ l αs ⟦k⟧)))]
        [(-provide specs)
         (match (map ↓pc specs)
           ['() (↓ₚᵣₘ -void)]
           [(cons ⟦spec⟧ ⟦spec⟧s)
            (λ (ρ $ Γ H Σ ⟦k⟧)
              (⟦spec⟧ ρ $ Γ H Σ (bgn∷ ⟦spec⟧s ρ ⟦k⟧)))])]
        [(? -e? e) (↓ₑ l e)]
        [_
         (log-warning "↓d : ignore ~a~n" (show-module-level-form d))
         (↓ₚᵣₘ -void)]))

    (match (map ↓d ds)
      ['() (↓ₚᵣₘ -void)]
      [(cons ⟦d⟧ ⟦d⟧s)
       (λ (ρ $ Γ H Σ ⟦k⟧)
         (⟦d⟧ ρ $ Γ H Σ (bgn∷ ⟦d⟧s ρ ⟦k⟧)))]))

  ;; Compile expression to computation
  (define (↓ₑ [l : -l] [e : -e]) : -⟦e⟧
    (let ↓ : -⟦e⟧ ([e : -e e])
      (remember-e!
       e
       (match e
         [(-λ xs e*)
          (define ⟦e*⟧ (memoize-⟦e⟧ (↓ e*)))
          (hash-set! ⟦e⟧-locs ⟦e*⟧ (locs e*))
          (set-bound-vars! ⟦e*⟧ (bv e*))
          (define fvs (fv e*))
          #;(printf "Warning: no longer canonicalize λ-term~n")
          (define t (-λ xs e*))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (define ρ* (m↓ ρ fvs))
            (define Γ*
              (∪ (for*/set: : -Γ ([φ (in-set Γ)]
                                  [fv⟦φ⟧ (in-value (fvₜ φ))]
                                  #:unless (set-empty? fv⟦φ⟧)
                                  #:when (⊆ fv⟦φ⟧ fvs))
                   φ)
                 ;; FIXME generalize HACK
                 (for*/union : -Γ ([x (in-hash-keys ρ)]
                                   [t (in-value (hash-ref $ x #f))]
                                   #:when t)
                   (for*/union : -Γ ([φ (in-set Γ)])
                      (match φ
                        [(-t.@ p (list (== t))) {set (-t.@ p (list (-t.x x)))}]
                        [(-t.@ p (list (? -b? b) (== t))) {set (-t.@ p (list b (-t.x x)))}]
                        [(-t.@ p (list (== t) (? -b? b))) {set (-t.@ p (list (-t.x x) b))}]
                        [_ ∅])))))
            (⟦k⟧ (-W (list (-Clo xs ⟦e*⟧ ρ* Γ*)) t) $ Γ H Σ))]
         [(-case-λ cases)
          (define ⟦mk⟧ (↓ₚᵣₘ 'scv:make-case-lambda))
          (define ⟦case⟧s (map ↓ cases))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦mk⟧ ρ $ Γ H Σ (ap∷ '() ⟦case⟧s ρ +ℓ₀ ⟦k⟧)))]
         [(? -prim? p) (↓ₚᵣₘ p)]
         [(-•)
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦k⟧ (-W (list (+●)) #f) $ Γ H Σ))]
         [(-x x ℓₓ)
          (match x
            [(? symbol? x)
             (↓ₓ l x ℓₓ)]
            [(and 𝒾 (-𝒾 x l₀))
             (: approximate-under-contract! : -Σ -V → -V)
             (define (approximate-under-contract! Σ V)
               (match V
                 [(-Ar C _ l³)
                  (match C
                    [(-=> (list (-⟪α⟫ℓ α₁ _)) (list (-⟪α⟫ℓ α₂ _)))
                     #:when (and (equal? (σ@ Σ α₁) {set 'any/c})
                                 (equal? (σ@ Σ α₂) {set 'boolean?}))
                     ;; cheat
                     V]
                    [_
                     (-Ar C (-α->⟪α⟫ (-α.imm (-Fn● (guard-arity C)))) l³)])]
                 [(-St* C _ l³)
                  (-St* C ⟪α⟫ₒₚ l³)]
                 [(-Vector/guard C _ l³)
                  (-Vector/guard C ⟪α⟫ₒₚ l³)]
                 [_ V]))
             
             (define-values (α modify-V)
               (cond
                 ;; same-module referencing returns unwrapped version
                 [(equal? l₀ l)
                  (values 𝒾 (λ ([Σ : -Σ] [V : -V]) V))]
                 ;; cross-module referencing returns wrapped version
                 ;; when the caller is symbolic (HACK)
                 ;; and supplies the negative monitoring context (HACK)
                 [(symbol? l)
                  (values (-α.wrp 𝒾) (λ ([Σ : -Σ] [V : -V]) (with-negative-party l V)))]
                 ;; cross-mldule referencing returns abstracted wrapped version
                 ;; when the caller is concrete (HACK)
                 ;; and supplies the negative monitoring context (HACK)
                 [else
                  (values (-α.wrp 𝒾) (λ ([Σ : -Σ] [V : -V])
                                       (with-positive-party 'dummy+
                                         (with-negative-party l
                                           (approximate-under-contract! Σ V)))))]))
             
             (define ⟪α⟫ (-α->⟪α⟫ α))
             (define ?loc (hack:α->loc ⟪α⟫))

             (λ (ρ $ Γ H Σ ⟦k⟧)
               (unless (hash-has-key? (-Σ-σ Σ) ⟪α⟫ₒₚ) ; HACK
                 (σ⊕V! Σ ⟪α⟫ₒₚ (+●)))
               (cond
                 [?loc
                  (define-values (Ws $*) ($@! Σ Γ ⟪α⟫ $ ?loc ℓₓ))
                  (for/union : (℘ -ς) ([W (in-set Ws)])
                             (⟦k⟧ (W¹->W W) $* Γ H Σ))]
                 [else
                  (for/union : (℘ -ς) ([V (in-set (σ@ Σ ⟪α⟫))])
                             (define V* (modify-V Σ V))
                             (⟦k⟧ (-W (list V*) ℓₓ) $ Γ H Σ))]))])]
         [(-@ f xs ℓ)
          (define ⟦f⟧  (↓ f))
          (define ⟦x⟧s (map ↓ xs))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦f⟧ ρ $ Γ H Σ (ap∷ '() ⟦x⟧s ρ ℓ ⟦k⟧)))]
         [(-if e₀ e₁ e₂)
          (define ⟦e₀⟧ (↓ e₀))
          (define ⟦e₁⟧ (↓ e₁))
          (define ⟦e₂⟧ (↓ e₂))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦e₀⟧ ρ $ Γ H Σ (if∷ l ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
         [(-wcm k v b) (error '↓ₑ "TODO: wcm")]
         [(-begin es)
          (match (map ↓ es)
            ['()
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦k⟧ (+W (list -void)) $ Γ H Σ))]
            [(cons ⟦e⟧ ⟦e⟧s)
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦e⟧ ρ $ Γ H Σ (bgn∷ ⟦e⟧s ρ ⟦k⟧)))])]
         [(-begin0 e₀ es)
          (define ⟦e₀⟧ (↓ e₀))
          (define ⟦e⟧s (map ↓ es))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦e₀⟧ ρ $ Γ H Σ (bgn0.v∷ ⟦e⟧s ρ ⟦k⟧)))]
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
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (define ⟦k⟧* (restore-$∷ ($-extract $ bounds) ⟦k⟧))
               (⟦e⟧ₓₛ ρ $ Γ H Σ (let∷ ℓ xs ⟦bnd⟧s* '() ⟦e*⟧ ρ ⟦k⟧*)))])]
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
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (define ρ* ; with side effect widening store
                 (for*/fold ([ρ  : -ρ  ρ])
                            ([⟦bnd⟧ ⟦bnd⟧s]
                             [xs (in-value (car ⟦bnd⟧))]
                             [x xs])
                   (define α (-α->⟪α⟫ (-α.x x H ∅)))
                   (σ⊕V! Σ α -undefined)
                   (ρ+ ρ x α)))
               (define ⟦k⟧* (restore-$∷ ($-extract $ bounds) ⟦k⟧))
               (⟦e⟧ₓₛ ρ* $ Γ H Σ (letrec∷ ℓ xs ⟦bnd⟧s* ⟦e*⟧ ρ* ⟦k⟧*)))])]
         [(-set! x e*)
          (define ⟦e*⟧ (↓ e*))
          (cond
            [(symbol? x)
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦e*⟧ ρ $ Γ H Σ (set!∷ (ρ@ ρ x) ⟦k⟧)))]
            [else
             (define α (-α->⟪α⟫ x))
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦e*⟧ ρ $ Γ H Σ (set!∷ α ⟦k⟧)))])]
         [(-error msg ℓ)
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦k⟧ (-blm (ℓ-src ℓ) 'Λ '() (list (-b msg)) ℓ) $ Γ H Σ))]
         [(-μ/c x c)
          (define ⟦c⟧ (↓ c))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (define α (-α->⟪α⟫ (-α.x/c x H)))
            (⟦c⟧ (ρ+ ρ x α) $ Γ H Σ (μ/c∷ x ⟦k⟧)))]
         [(--> cs d ℓ)
          (define ⟦d⟧ (↓ d))
          (match (-var-map ↓ cs)
            ['()
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦d⟧ ρ $ Γ H Σ (-->.rng∷ '() #f ℓ ⟦k⟧)))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (⟦c⟧ ρ $ Γ H Σ (-->.dom∷ '() ⟦c⟧s #f ⟦d⟧ ρ ℓ ⟦k⟧)))]
            [(-var ⟦c⟧s ⟦c⟧ᵣ)
             (match ⟦c⟧s
               ['()
                (λ (ρ $ Γ H Σ ⟦k⟧)
                  (⟦c⟧ᵣ ρ $ Γ H Σ (-->.rst∷ '() ⟦d⟧ ρ ℓ ⟦k⟧)))]
               [(cons ⟦c⟧ ⟦c⟧s*)
                (λ (ρ $ Γ H Σ ⟦k⟧)
                  (⟦c⟧ ρ $ Γ H Σ (-->.dom∷ '() ⟦c⟧s* ⟦c⟧ᵣ ⟦d⟧ ρ ℓ ⟦k⟧)))])])]
         [(-->i cs (and mk-d (-λ xs d)) ℓ)
          (define ⟦d⟧ (↓ d))
          (match (map ↓ cs)
            ['()
             (define c (-?->i '() mk-d))
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
               (define-values (G g) (mk-=>i! Σ Γ H '() Mk-D mk-d ℓ))
               (⟦k⟧ (-W (list G) g) $ Γ H Σ))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (define Mk-D (-Clo xs ⟦d⟧ ρ Γ))
               (⟦c⟧ ρ $ Γ H Σ (-->i∷ '() ⟦c⟧s ρ Mk-D mk-d ℓ ⟦k⟧)))])]
         [(-case-> cases)
          (define ⟦case⟧s (map ↓ cases))
          (define ⟦mk⟧ (↓ₚᵣₘ 'scv:make-case->))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦mk⟧ ρ $ Γ H Σ (ap∷ '() ⟦case⟧s ρ #|dummy|# +ℓ₀ ⟦k⟧)))]
         [(-∀/c xs e*)
          (define ⟦e*⟧ (↓ e*))
          (define fvs (fv e*))
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (define ρ* (m↓ ρ fvs))
            (⟦k⟧ (-W (list (-∀/C xs ⟦e*⟧ ρ*)) #f) $ Γ H Σ))]
         [(-x/c x)
          (λ (ρ $ Γ H Σ ⟦k⟧)
            (⟦k⟧ (-W (list (-x/C (ρ@ ρ x))) #f) $ Γ H Σ))]
         [(-struct/c 𝒾 cs ℓ)
          (define α (-α->⟪α⟫ 𝒾))
          (define blm (-blm l 'Λ '(struct-defined?) (list (-𝒾-name 𝒾)) ℓ))
          (define builtin-struct-tag? (match? 𝒾 (== -𝒾-cons) (== -𝒾-box)))
          (match (map ↓ cs)
            ['()
             (define W (-W (list (-St/C #t 𝒾 '())) (-t.@ (-st/c.mk 𝒾) '())))
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (define A (if (or builtin-struct-tag? (defined-at? Σ α)) W blm))
               (⟦k⟧ A $ Γ H Σ))]
            [(cons ⟦c⟧ ⟦c⟧s)
             (λ (ρ $ Γ H Σ ⟦k⟧)
               (if (or builtin-struct-tag? (defined-at? Σ α))
                   (⟦c⟧ ρ $ Γ H Σ (struct/c∷ ℓ 𝒾 '() ⟦c⟧s ρ ⟦k⟧))
                   (⟦k⟧ blm $ Γ H Σ)))])]
         [_ (error '↓ₑ "unhandled: ~a" (show-e e))])))

    )

  (define/memo (↓ₓ [l : -l] [x : Symbol] [ℓₓ : ℓ]) : -⟦e⟧
    (define -blm.undefined
      (-blm l 'Λ (list 'defined?) (list (format-symbol "~a_(~a)" 'undefined x)) ℓₓ))
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (define α (ρ@ ρ x))
      (cond
        [(-V? α)
         (⟦k⟧ (-W (list α) x) $ Γ H Σ)]
        [else
         (define-values (Ws $*) ($@! Σ Γ α $ x ℓₓ))
         (for/union : (℘ -ς) ([W (in-set Ws)])
           (define A
             (match W
               [(-W¹ (-b (== undefined)) _) -blm.undefined]
               [(-W¹ V                   t) (-W (list V) t)]))
           (⟦k⟧ A $* Γ H Σ))])))

  (define (↓ₚᵣₘ [p : -prim]) (ret-W¹ p p))

  (define/memo (ret-W¹ [V : -V] [t : -?t]) : -⟦e⟧
    (define W (-W (list V) t))
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (⟦k⟧ W $ Γ H Σ)))

  (define/memo (mk-mon [ctx : -ctx] [⟦c⟧ : -⟦e⟧] [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (⟦c⟧ ρ $ Γ H Σ (mon.v∷ ctx (cons ⟦e⟧ ρ) ⟦k⟧))))

  (define/memo (mk-app [ℓ : ℓ] [⟦f⟧ : -⟦e⟧] [⟦x⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (⟦f⟧ ρ $ Γ H Σ (ap∷ '() ⟦x⟧s ρ ℓ ⟦k⟧))))

  (define/memo (mk-rt [A : (U -A -W¹)]) : -⟦e⟧
    (match A
      [(-W¹ V v) (mk-rt (-W (list V) v))]
      [(? -A?) (λ (_ $ Γ H Σ ⟦k⟧) (⟦k⟧ A $ Γ H Σ))]))

  (define/memo (mk-fc [l : -l] [ℓ : ℓ] [⟦c⟧ : -⟦e⟧] [⟦v⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (⟦c⟧ ρ $ Γ H Σ (fc.v∷ l ℓ ⟦v⟧ ρ ⟦k⟧))))

  (define/memo (mk-wrapped-hash [C : -Hash/C] [ctx : -ctx] [α : ⟪α⟫] [W : -W¹]) : -⟦e⟧
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (match-define (-W¹ V t) W)
      (σ⊕V! Σ α V)
      (⟦k⟧ (-W (list (-Hash/guard C α ctx)) t) $ Γ H Σ)))

  (define/memo (mk-wrapped-set [C : -Set/C] [ctx : -ctx] [α : ⟪α⟫] [W : -W¹]) : -⟦e⟧
    (λ (ρ $ Γ H Σ ⟦k⟧)
      (match-define (-W¹ V t) W)
      (σ⊕V! Σ α V)
      (⟦k⟧ (-W (list (-Set/guard C α ctx)) t) $ Γ H Σ)))
  )

