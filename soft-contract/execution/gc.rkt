#lang typed/racket/base

(provide gc@)

(require racket/set
         racket/match
         typed/racket/unit
         set-extras
         unreachable
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit gc@
  (import meta-functions^
          exec^ pretty-print^
          val^)
  (export gc^)

  (: gc : (℘ T) Σ → Σ)
  (define (gc root Σ₀)
    (define seen : (Mutable-HashTable T #t) (make-hash))

    (define Ts-from-α
      (for*/fold ([m : (HashTable α (℘ T)) (hash)])
                 ([Tᵢ (in-hash-keys Σ₀)]
                  #:when (T:@? Tᵢ)
                  [α (in-set (T-root Tᵢ))])
        (hash-update m α (λ ([Ts : (℘ T)]) (set-add Ts Tᵢ)) mk-∅)))

    (: touch : T Σ → Σ)
    (define (touch T Σ)
      (if (hash-has-key? seen T)
          Σ
          (let ([T* (cond [(T:@? T) (T-root T)]
                          [(-b? T) ∅]
                          [else (hash-ref Ts-from-α T mk-∅)])])
            (hash-set! seen T #t)
            (define Σ*
              (match (hash-ref Σ₀ T #f)
                [(and r (cons Vs _)) (foldl touch* (hash-set Σ T r) (set-map Vs V-root))]
                [#f Σ]))
            (touch* T* Σ*))))
    
    (: touch* : (℘ T) Σ → Σ)
    (define (touch* Ts Σ) (set-fold touch Σ Ts))

    (let ([Σ* (touch* root ⊥Σ)])
      (if (= (hash-count Σ*) (hash-count Σ₀))
          ;; Try to re-use old instance
          Σ₀
          ;; Remove refinements referring to gc-ed values
          (let ([root* (list->set (hash-keys Σ*))])
            (for/fold ([Σ* : Σ Σ*]) ([(T r) (in-hash Σ*)])
              (match-define (cons Vs N) r)
              (define Vs*
                (for/fold ([Vs* : V^ Vs]) ([V (in-set Vs)])
                  (match V
                    [(-● Ps)
                     (define Ps*
                       (for*/fold ([Ps* : (℘ P) Ps]) ([P (in-set Ps)]
                                                      [P:root (in-value (P-root P))]
                                                      #:unless (or (set-empty? P:root)
                                                                   (⊆ P:root root*)))
                         (set-remove Ps* P)))
                     ;; Try to retain old instance
                     (if (eq? Ps* Ps) Vs* (set-add (set-remove Vs* V) (-● Ps*)))]
                    [_ Vs*])))
              (cond [(eq? Vs* Vs) Σ*] ; try to retain old instance
                    [(set-empty? Vs*) (hash-remove Σ* T)]
                    [else (hash-set Σ* T (cons Vs* N))]))))))

  (: with-gc : (℘ T) (→ (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (with-gc root comp)
    (define-values (r es) (comp))
    (values (gc-R root r) es))

  (: gc-R : (℘ T) R → R)
  (define (gc-R root r)
    (for/fold ([acc : R ⊥R]) ([(ΔΣ Ws) (in-hash r)])
      (define root* (apply ∪ root (set-map Ws W-root)))
      (define ΔΣ* (gc root* ΔΣ))
      (hash-update acc ΔΣ* (λ ([Ws₀ : (℘ W)]) (∪ Ws₀ Ws)) mk-∅)))

  (define V-root : (V → (℘ T))
    (match-lambda
      [(St _ αs) (list->set αs)]
      [(Vect αs) (list->set αs)]
      [(Vect-Of αₑ Vₙ) (set-add (set-filter α? Vₙ) αₑ)]
      [(Hash-Of αₖ αᵥ _) {set αₖ αᵥ}]
      [(Set-Of α _) {set α}]
      [(Clo _ E Ρ _) (∪ Ρ (set-filter (match-lambda [(γ:lex (? symbol?)) #f] [_ #t]) (E-root E)))]
      [(Case-Clo clos _) (apply ∪ ∅ (map Clo-_2 clos))]
      [(Guarded _ C α) (set-add (V-root C) α)]
      [(Sealed α) ∅] ; TODO confirm ok
      [(And/C α₁ α₂ _) {set α₁ α₂}]
      [(Or/C α₁ α₂ _) {set α₁ α₂}]
      [(Not/C α _) {set α}]
      [(X/C α) {set α}]
      [(Seal/C α) {set α}]
      [(St/C _ αs _) (list->set αs)]
      [(Vectof/C α _) {set α}]
      [(Vect/C αs _) (list->set αs)]
      [(Hash/C αₖ αᵥ _) {set αₖ αᵥ}]
      [(Set/C α _) {set α}]
      [(? ==>i? V) (==>i-root V)]
      [(∀/C _ _ Ρ) Ρ]
      [(Case-=> Cs) (apply ∪ ∅ (map ==>i-root Cs))]
      [(? α? α) {set α}]
      [(? T:@? T) (T-root T)]
      [(? P? P) (P-root P)]
      [(-● Ps) ∅]
      [(-st-ac 𝒾 i) {set (γ:escaped-field 𝒾 i)}]
      [(? symbol? o) {set (γ:hv o)}]
      [(? -prim? p) ∅]))

  (define P-root : (P → (℘ T))
    (match-lambda
      [(P:¬ Q) (P-root Q)]
      [(or (P:> T) (P:≥ T) (P:< T) (P:≤ T) (P:= T)) (if (T? T) {set T} ∅)]
      [_ ∅]))

  (: V^-root : V^ → (℘ T))
  (define (V^-root Vs) (set-union-map V-root Vs))

  (: W-root : W → (℘ T))
  (define (W-root W) (apply ∪ ∅ (map V^-root W)))

  (define ==>i-root : (==>i → (℘ T))
    (match-lambda
      [(==>i (-var doms ?doms:rst) rng)
       (∪ (apply ∪ (if ?doms:rst (Dom-root ?doms:rst) ∅) (map Dom-root doms))
          (if rng (apply ∪ ∅ (map Dom-root rng)) ∅))]))

  (define Dom-root : (Dom → (℘ T))
    (match-lambda [(Dom _ C _) (if (Clo? C) (Clo-_2 C) {set C})]))

  (: E-root : E → (℘ γ))
  ;; Compute free variables for expression. Return set of variable names.
  (define E-root
    (match-lambda
      [(? symbol? o) {set (γ:hv o)}]
      [(-st-ac 𝒾 i) {set (γ:escaped-field 𝒾 i)}]
      [(? -•?) {set (γ:hv #f)}]
      [(-x x ℓ)
       {set (cond [(symbol? x) (γ:lex x)]
                  [(equal? (ℓ-src ℓ) (-𝒾-src x)) (γ:top x)]
                  [else (γ:wrp x)])}]
      [(-λ xs e _) (set-subtract (E-root e) (map/set γ:lex (formals->names xs #:eq? #f)))]
      [(-case-λ cases _) (apply ∪ ∅ (map E-root cases))]
      [(-@ f xs _) (apply ∪ (E-root f) (map E-root xs))]
      [(-begin es) (apply ∪ ∅ (map E-root es))]
      [(-begin0 e₀ es) (apply ∪ (E-root e₀) (map E-root es))]
      [(-let-values bnds e _)
       (define-values (bound rhs:E-root)
         (for/fold ([bound : (℘ γ) ∅] [rhs:E-root : (℘ γ) ∅])
                   ([bnd bnds])
           (match-define (cons xs rhs) bnd)
           (values (set-add* bound (map γ:lex xs)) (∪ rhs:E-root (E-root rhs)))))
       (∪ rhs:E-root (set-subtract (E-root e) bound))]
      [(-letrec-values bnds e _)
       (define bound (for/fold ([bound : (℘ γ) ∅]) ([bnd bnds])
                       (set-add* bound (map γ:lex (car bnd)))))
       (set-subtract (apply ∪ (E-root e) (map (compose1 E-root (inst cdr Any -e)) bnds)) bound)]
      [(-set! x e _) (E-root e)]
      [(-if e e₁ e₂ _) (∪ (E-root e) (E-root e₁) (E-root e₂))]
      [(-μ/c _ e) (E-root e)]
      [(-->i (-var cs c) d)
       (define dom-E-root : (-dom → (℘ γ))
         (match-lambda
           [(-dom _ ?xs d _) (set-subtract (E-root d) (if ?xs (list->set (map γ:lex ?xs)) ∅))]))
       (∪ (apply ∪ (if c (dom-E-root c) ∅) (map dom-E-root cs))
          (if d (apply ∪ ∅ (map dom-E-root d)) ∅))]
      [(case--> cases) (apply ∪ ∅ (map E-root cases))]
      [E (log-debug "E-ROOT⟦~a⟧ = ∅~n" E) ∅]))

  )
