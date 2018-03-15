(splicing-local
      ()

    (: mk-=> : -Σ -H -φ (Listof -V^) (Option -V^) (Listof -V^) ℓ → (Values -V -φ))
    (define (mk-=> Σ H φ doms.rev rst rngs ℓ) 
      (define-values (Dom φ₁)
        (let-values ([(Init φ*) (mk-⟪α⟫ℓ* Σ 'dom -α.dom H ℓ φ (reverse doms.rev))])
          (cond [rst (define αᵣ (-α->⟪α⟫ (-α.rst ℓ H)))
                     (define ℓᵣ (ℓ-with-id ℓ 'rest))
                     (values (-var Init (-⟪α⟫ℓ αᵣ ℓᵣ)) (alloc Σ φ* αᵣ rst))]
                [else (values Init φ*)])))
      (define-values (Rng φ₂)
        (match rngs
          ['(any) (values 'any φ₁)]
          [_ (mk-⟪α⟫ℓ* Σ 'rng -α.rng H ℓ φ₁ rngs)]))
      (values (-=> Dom Rng) φ₂))

    ) 

  (define/memo (hv∷ [tag : HV-Tag] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define φ* (add-leak! tag Σ φ A))
      {set (-ς↑ (σₖ+! Σ (-αₖ H (-HV tag) φ*) ⟦k⟧))}))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helper frames
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-frame (mon-or/c∷ [ctx : -ctx] [Cₗ : -V^] [Cᵣ : -V^] [V : -V^] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Cₗ Cᵣ V)
      (match A
        [(list _)
         (for/union : (℘ -ς) ([C (in-set Cₗ)])
            (push-mon ctx Cᵣ (V- (-Σ-σ Σ) φ V C) H φ Σ ⟦k⟧))]
        [(list _ V)
         (define Vₐ (for/union : -V^ ([C (in-set Cₗ)])
                      (V+ (-Σ-σ Σ) φ V C)))
         (⟦k⟧ (list Vₐ) H φ Σ)])))

(define-frame (if.flat/c∷ [V* : -V^] [blm : -blm] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (V*)
      (match A
        [(list V^)
         (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ 'values V^)]) : -ς
           #:true  (⟦k⟧ (list V*) H φ₁ Σ)
           #:false (⟦k⟧ blm       H φ₂ Σ))]
        [_
         (match-define (-blm _ lo _ _ ℓ) blm)
         (⟦k⟧ (blm/simp lo 'Λ '(|1 value|) A ℓ) H φ Σ)])))

  (define-frame (fc-and/c∷ [l : -l]
                           [ℓ : ℓ]
                           [C₁ : -V^]
                           [C₂ : -V^]
                           [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C₁ C₂)
      (match A
        [(list _) (⟦k⟧ (list {set -ff}) H φ Σ)]
        [(list _ V)
         (define Vₐ (for/union : -V^ ([C (in-set C₁)])
                       (V+ (-Σ-σ Σ) φ V C)))
         (push-fc l ℓ C₂ Vₐ H φ Σ ⟦k⟧)])))

  (define-frame (fc-or/c∷ [l : -l]
                          [ℓ : ℓ]
                          [C₁ : -V^]
                          [C₂ : -V^]
                          [V : -V^]
                          [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C₁ C₂)
      (match A
        [(list _)
         (push-fc l ℓ C₂ V H φ Σ ⟦k⟧)]
        [(list _ V)
         (define Vₐ (for/union : -V^ ([C (in-set C₁)]) (V+ (-Σ-σ Σ) φ V C)))
         (⟦k⟧ (list {set -tt} Vₐ) H φ Σ)])))

  (define-frame (fc-not/c∷ [V^ : -V^] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (V^)
      (match A
        [(list _)
         (⟦k⟧ (list {set -tt} V^) H φ Σ)]
        [(list _ _)
         (⟦k⟧ (list {set -ff}) H φ Σ)])))

  (define-frame (fc-struct/c∷ [l : -l]
                              [ℓ : ℓ]
                              [𝒾 : -𝒾]
                              [Vs-rev : (Listof -V^)]
                              [⟦e⟧s : (Listof -⟦e⟧)]
                              [ρ : -ρ]
                              [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (Vs-rev ρ)
      (match A
        [(list _)
         (⟦k⟧ (list {set -ff}) H φ Σ)]
        [(list _ V*)
         (match ⟦e⟧s
           ['()
            (define ⟦k⟧*
              (let ([k (-st-mk 𝒾)])
                (ap∷ (append Vs-rev (list {set k})) '() ⊥ρ ℓ
                     (ap∷ (list {set -tt} {set 'values}) '() ⊥ρ ℓ ⟦k⟧))))
            (⟦k⟧* (list V*) H φ Σ)]
           [(cons ⟦e⟧ ⟦e⟧s*)
            (⟦e⟧ ρ H φ Σ (fc-struct/c∷ l ℓ 𝒾 (cons V* Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

  (define-frame (fc.v∷ [l : -l]
                       [ℓ : ℓ]
                       [⟦v⟧ : -⟦e⟧]
                       [ρ : -ρ]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (ρ)
      (match A
        [(list C)
         (⟦v⟧ ρ H φ Σ (fc.c∷ l ℓ C ⟦k⟧))]
        [_
         (⟦k⟧ (blm/simp l 'Λ '(|1 value|) A ℓ) H φ Σ)])))

  (define-frame (fc.c∷ [l : -l]
                       [ℓ : ℓ]
                       [C : -V^]
                       [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots (C)
      (match A
        [(list V)
         (push-fc l ℓ C V H φ Σ ⟦k⟧)]
        [_
         (define blm (blm/simp l 'Λ '(|1 value|) A ℓ))
         (⟦k⟧ blm H φ Σ)])))

  (define-frame (restore-ctx∷ [H : -H] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A _ φ Σ) #:roots ()
      (⟦k⟧ A H φ Σ)))

  (define-frame (hash-set-inner∷ [ℓ : ℓ] [αₕ : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ((box αₕ))
      (match-define (list Vₖ Vᵥ) A)
      (app ℓ {set 'hash-set} (list (σ@ Σ (-φ-cache φ) αₕ) Vₖ Vᵥ) H φ Σ ⟦k⟧)))

  (define-frame (set-add-inner∷ [ℓ : ℓ] [αₛ : ⟪α⟫] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ((box αₛ))
      (match-define (list Vₑ) A)
      (define Vₛ (σ@ Σ (-φ-cache φ) αₛ))
      (app ℓ {set 'set-add} (list Vₛ Vₑ) H φ Σ ⟦k⟧)))

  (define-frame (maybe-havoc-prim-args∷ [ℓ : ℓ] [o : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define σ (-Σ-σ Σ))
      (define behavioral-args
        (for*/set: : -V^ ([V^ (in-list A)]
                          [V (in-set V^)]
                          #:when (behavioral? σ (-φ-cache φ) V))
          V))
      (if (set-empty? behavioral-args)
          (⟦k⟧ A H φ Σ)
          (app (ℓ-with-id ℓ 'prim-havoc)
               {set (-Fn● 1 (cons o H))}
               (list behavioral-args)
               H φ Σ
               (bgn0.e∷ A '() ⊥ρ ⟦k⟧)))))

  (define-frame (make-prim-range∷ [ctx : -ctx]
                                  [?rng-wrap : (Option (Listof -⟪α⟫ℓ))]
                                  [ranges : (Listof -V^)]
                                  [cases : (Listof (List (Listof -V) (Option -V) (Listof -V)))]
                                  [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define-values (refined-ranges φ*)
        (let-values ([(ranges₀ φ₀) (maybe-refine ranges (-Σ-σ Σ) φ cases A)])
          (hack:maybe-refine-more (assert (-ctx-src ctx) -o?) ranges₀ (-Σ-σ Σ) φ₀ A)))
      (define ⟦k⟧* (if ?rng-wrap (mon*.c∷ ctx ?rng-wrap ⟦k⟧) ⟦k⟧))
      (⟦k⟧* refined-ranges H φ* Σ)))

(define-frame (implement-predicate∷ [o : Symbol] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (⟦k⟧ (list (implement-predicate (-Σ-σ Σ) φ o A)) H φ Σ)))

  (define-frame (absurd∷ [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
       ∅))

  (define-frame (rename∷ [uni : Uni] [Γₑᵣ : -Γ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
       (match-define (Bij er->ee ee->er) uni)
       (define Vs : (Listof -V^)
         (for/list ([V^ (in-list A)])
           (rename-V^ ee->er (discard-conflicting-names uni (-φ-condition φ) V^))))
       (define φ*
         (match-let ([(-φ Γₑₑ δσ) φ])
           ;; "translate" callee's proposition into caller's
           (define Γ₁ (Γ+ Γₑᵣ ee->er Γₑₑ))
           ;; result may share the same symbolic name, thus absent in `m`
           (define Γ₂
             (for*/fold ([Γ : -Γ Γ₁])
                        ([V^ (in-list A)]
                         [V (in-set V^)]
                         #:when (-t? V)
                         #:unless (hash-has-key? ee->er V)
                         #:unless (hash-has-key? er->ee V)
                         [ps (in-value (hash-ref Γₑₑ V #f))]
                         #:when ps)
               (hash-update Γ V (λ ([ps₀ : (℘ -h)]) (∪ ps₀ ps)) mk-∅)))
           (-φ Γ₂ δσ)))
       (⟦k⟧ Vs H φ* Σ)))

  (define-frame (maybe-unshadow∷ [δσ : -δσ] [dependencies : -δσ] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A H φ Σ) #:roots ()
      (define φ*
        (match-let ([(-φ Γ δσ₀) φ])
          (define δσ₁
            (for/fold ([δσ* : -δσ δσ₀])
                      ([(α V) (in-hash δσ)]
                       #:unless (equal? 'N (cardinality (-Σ-σ Σ) δσ₀ α)))
              (hash-set δσ* α V)))
          (define δσ₂
            (for/fold ([δσ* : -δσ δσ₁])
                      ([(α V) (in-hash dependencies)])
              (hash-update δσ* α (λ ([V₀ : -V^]) (V⊕ φ V₀ V)) mk-∅)))
          (-φ Γ δσ₂)))
      (⟦k⟧ A H φ* Σ)))

  (: maybe-refine : (Listof -V^) -σ -φ (Listof (List (Listof -V) (Option -V) (Listof -V))) (Listof -V^) → (Values (Listof -V^) -φ))
  (define (maybe-refine rng₀ σ φ cases args)

    (: ⊢/quick : -V -V^ → -R)
    (define (⊢/quick o V^)
      (match o
        [(-Not/C (-⟪α⟫ℓ (app ⟪α⟫->-α (-α.imm C)) _)) (not-R (⊢/quick C V^))]
        [(? -h? p)                                   (quick-p∋V^ σ φ p V^)]
        [_ '?]))

    (for/fold ([rng : (Listof -V^) rng₀] [φ : -φ φ])
              ([kase (in-list cases)])
      (match-define (list dom-inits ?dom-rst refinements) kase)
      (: check-inits : (Listof -V) (Listof -V^) → (Values (Listof -V^) -φ))
      (define (check-inits doms args)
        (match* (doms args)
          [((cons dom doms*) (cons arg args*))
           (case (⊢/quick dom arg)
             [(✓) (check-inits doms* args*)]
             [else (values rng φ)])]
          [('() _) (check-rest args)]
          [((cons _ _) '()) (values rng φ)]))
      (: check-rest : (Listof -V^) → (Values (Listof -V^) -φ))
      (define (check-rest args)
        (cond
          [?dom-rst
           (let go : (Values (Listof -V^) -φ) ([args : (Listof -V^) args])
            (match args
              ['() (refine-rng)]
              [(cons arg args*)
               (case (⊢/quick ?dom-rst arg)
                 [(✓) (go args*)]
                 [else (values rng φ)])]))]
          [else (if (null? args) (refine-rng) (values rng φ))]))
      (define (refine-rng)
        (let-values ([(Vs-rev φ*)
                      (for/fold ([Vs-rev : (Listof -V^) '()] [φ : -φ φ])
                                ([rngᵢ (in-list rng)]
                                 [refᵢ (in-list refinements)])
                        (values (cons (V+ σ φ rngᵢ refᵢ) Vs-rev)
                                (if (-h? refᵢ)
                                    (match rngᵢ
                                      [(singleton-set Vᵢ) (φ+pV φ refᵢ (list Vᵢ))]
                                      [_ φ])
                                    φ)))])
          (values (reverse Vs-rev) φ*)))
      (check-inits dom-inits args)))

(: hack:maybe-refine-more : -o (Listof -V^) -σ -φ (Listof -V^) → (Values (Listof -V^) -φ))
  ;; This hack should be removed once the primitives DSL is generalized to be able
  ;; to express these properties
  (define (hack:maybe-refine-more o rngs σ φ args)
    (: obvious? : -o -V^ * → Boolean)
    (define (obvious? o . Vs)
      (equal? '✓ (apply quick-p∋V^ σ φ o Vs)))
    
    (match* (o args)
      ;; ord(V₁+V₂, V₁) if ord(V₂, 0)
      [('+ (list (singleton-set (? -t? t)) (singleton-set (and V (not (? -t?))))))
       (define 0^ {set -zero})
       (define-set res : -h)
       (define V^ {set V})
       (cond [(obvious? '>  V^ 0^) (res-add! (->/c t))]
             [(obvious? '>= V^ 0^) (res-add! (-≥/c t))]
             [(obvious? '<  V^ 0^) (res-add! (-</c t))]
             [(obvious? '<= V^ 0^) (res-add! (-≤/c t))]
             [else (void)])
       (match-define (list rng) rngs)
       (values (list (for/fold ([rng : -V^ rng]) ([ref (in-set res)])
                       (V+ σ φ rng ref)))
               (match rng
                 [(singleton-set V)
                  (for/fold ([φ : -φ φ]) ([ref (in-set res)] #:when (-h? ref))
                    (φ+pV φ ref (list V)))]
                 [_ φ]))]
      [('+ (list (and V₁^ (singleton-set (not (? -t?)))) (and V₂^ (singleton-set (? -t?)))))
       (hack:maybe-refine-more o rngs σ φ (list V₂^ V₁^))]
      [(_ _)
       (values rngs φ)]))

(: mk-⟪α⟫ℓ* : -Σ Symbol (ℓ -H Index → -α) -H ℓ -φ (Listof -V^) → (Values (Listof -⟪α⟫ℓ) -φ))
  (define (mk-⟪α⟫ℓ* Σ tag mk-α H ℓ φ Vs)
    (define-values (αℓs φ*)
      (for/fold ([αℓs-rev : (Listof -⟪α⟫ℓ) '()] [φ : -φ φ])
                ([V (in-list Vs)] [i (in-naturals)] #:when (index? i))
        (define α (-α->⟪α⟫ (mk-α ℓ H i)))
        (define αℓ (-⟪α⟫ℓ α (ℓ-with-id ℓ (cons tag i))))
        (values (cons αℓ αℓs-rev) (alloc Σ φ α V))))
    (values (reverse αℓs) φ*))

  


  )
