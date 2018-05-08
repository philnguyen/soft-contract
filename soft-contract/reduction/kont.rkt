  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helper frames
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-frame (restore-ctx∷ [H : -H] [⟦k⟧ : -⟦k⟧])
    (make-frame (⟦k⟧ A _ φ Σ) #:roots ()
      (⟦k⟧ A H φ Σ)))

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
  )
