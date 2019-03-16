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
  (import meta-functions^ static-info^
          exec^
          sto^ val^)
  (export gc^)

  (: gc ([(℘ α) Σ] [Σ] . ->* . Σ))
  ;; Garbage collect store(-delta) `Σ₀` with respect to live addresses `root`.
  ;; The context `Σ-ctx` is the full store, which may or may not coincide with `Σ₀`
  (define (gc root Σ₀ [ctx Σ₀])
    (define-set touched : α)

    (: touch : α Σ → Σ)
    (define (touch α Σ)
      (touched-add! α)
      ;; Look up full context to span addresses,
      ;; but only copy entries from the store-delta in focus
      (define Vs (Σ@ α ctx))
      (define Σ*
        (match (hash-ref Σ₀ α #f)
          [(? values r) (hash-set Σ α r)]
          [#f Σ]))
      (for*/fold ([Σ* : ΔΣ Σ*])
                 ([V (in-set Vs)]
                  [α* (in-set (V-root V))] #:unless (touched-has? α*))
        (touch α* Σ*)))

    (let ([Σ* (set-fold touch ⊥Σ root)])
      (if (= (hash-count Σ*) (hash-count Σ₀))
          ;; Try to re-use old instance
          Σ₀
          (remove-stale-refinements touched Σ*))))

  (: remove-stale-refinements : (℘ α) Σ → Σ)
  (define (remove-stale-refinements root Σ₁)
    (for/fold ([Σ₁ : Σ Σ₁]) ([(α r) (in-hash Σ₁)])
      (match-define (cons Vs N) r)
      (define Vs*
        (for/fold ([Vs* : V^ Vs]) ([Vᵢ (in-set Vs)])
          (: replace-if-refinements-stale : (℘ P) ((℘ P) → V) → V^)
          (define (replace-if-refinements-stale Ps mk-V)
            (define Ps*
              (for*/fold ([Ps* : (℘ P) Ps]) ([P (in-set Ps)] #:unless (⊆ (P-root P) root))
                (set-remove Ps* P)))
            ;; Try to reuse old instance
            (if (eq? Ps* Ps) Vs* (set-add (set-remove Vs* Vᵢ) (mk-V Ps*))))
          (match Vᵢ
            [(-● Ps) (replace-if-refinements-stale Ps -●)]
            [(St 𝒾 αs Ps)
             (replace-if-refinements-stale Ps (λ (Ps*) (St 𝒾 αs Ps*)))]
            [_ Vs*])))
      (cond [(eq? Vs* Vs) Σ₁] ; try to reuse old instance
            [(set-empty? Vs*) (hash-remove Σ₁ α)]
            [else (hash-set Σ₁ α (cons Vs* N))])))

  (: with-gc : (℘ α) Σ (→ (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (with-gc root Σ comp)
    (define-values (r es) (comp))
    (values (gc-R root Σ r) es))

  (: gc-R : (℘ α) Σ R → R)
  (define (gc-R root Σ r)
    (for/hash : R ([(W ΔΣs) (in-hash r)])
      (define root* (∪ root (W-root W)))
      (values W (map/set (λ ([ΔΣ : ΔΣ]) (gc root* ΔΣ (⧺ Σ ΔΣ))) ΔΣs))))

  (define V-root : (V → (℘ α))
    (match-lambda
      [(St _ αs _) (list->set αs)]
      [(Vect αs) (list->set αs)]
      [(Vect-Of αₑ Vₙ) (set-add (set-filter α? Vₙ) αₑ)]
      [(Hash-Of αₖ αᵥ) {set αₖ αᵥ}]
      [(Set-Of α) {set α}]
      [(? Clo? V) (Clo-root V)]
      [(Case-Clo clos _) (apply ∪ ∅ (map Clo-root clos))]
      [(Guarded _ C α) (set-add (V-root C) α)]
      [(Sealed α) ∅] ; TODO confirm ok
      [(And/C α₁ α₂ _) {set α₁ α₂}]
      [(Or/C α₁ α₂ _) {set α₁ α₂}]
      [(Not/C α _) {set α}]
      [(X/C α) {set α}]
      [(Seal/C α _) {set α}]
      [(St/C 𝒾 αs _)
       (∪ (list->set αs)
          (if (prim-struct? 𝒾)
              ∅
              ;; TODO: this may not work properly with sub-structs
              (for/set: : (℘ α) ([i (in-range (count-struct-fields 𝒾))])
                (γ:escaped-field 𝒾 (assert i index?)))))]
      [(Vectof/C α _) {set α}]
      [(Vect/C αs _) (list->set αs)]
      [(Hash/C αₖ αᵥ _) {set αₖ αᵥ}]
      [(Set/C α _) {set α}]
      [(? ==>i? V) (==>i-root V)]
      [(∀/C _ _ Ρ _) Ρ]
      [(Case-=> Cs) (apply ∪ ∅ (map ==>i-root Cs))]
      [(? α? α) {set α}]
      [(? T:@? T) (T-root T)]
      [(-st-ac 𝒾 i) {set (γ:escaped-field 𝒾 i)}]
      [(? P? P) (P-root P)]
      [(? symbol? o) {set (γ:hv o)}]
      [(or (? -prim?) (? One-Of/C?) (? -●?) (? Empty-Set?) (? Empty-Hash?)) ∅]))

  (define Clo-root : (Clo → (℘ α))
    (match-lambda
      [(Clo _ E Ρ _) (∪ Ρ (set-filter (match-lambda [(γ:lex (? symbol?)) #f] [_ #t]) (E-root E)))]))

  (define P-root : (P → (℘ α))
    (match-lambda
      [(P:¬ Q) (P-root Q)]
      [(P:St _ P) (P-root P)]
      [(or (P:> T) (P:≥ T) (P:< T) (P:≤ T) (P:= T) (P:≡ T))
       (cond [(T:@? T) (T-root T)]
             [(α? T) {set T}]
             [else ∅])]
      [_ ∅]))

  (: V^-root : V^ → (℘ α))
  (define (V^-root Vs) (set-union-map V-root Vs))

  (: W-root : W → (℘ α))
  (define (W-root W) (apply ∪ ∅ (map V^-root W)))

  (define ==>i-root : (==>i → (℘ α))
    (match-lambda
      [(==>i (-var doms ?doms:rst) rng)
       (∪ (apply ∪ (if ?doms:rst (Dom-root ?doms:rst) ∅) (map Dom-root doms))
          (if rng (apply ∪ ∅ (map Dom-root rng)) ∅))]))

  (define Dom-root : (Dom → (℘ α))
    (match-lambda [(Dom _ C _) (if (Clo? C) (Clo-root C) {set C})]))

  (: E-root : E → (℘ γ))
  ;; Compute free variables for expression. Return set of variable names.
  (define E-root
    (let ([cache : (Mutable-HashTable E (℘ γ)) (make-hasheq)])
      (λ (E)
        (hash-ref!
         cache E
         (λ ()
           (match E
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
             [(-set! x e _) (set-add (E-root e) (if (symbol? x) (γ:lex x) (γ:top x)))]
             [(-if e e₁ e₂ _) (∪ (E-root e) (E-root e₁) (E-root e₂))]
             [(-μ/c _ e) (E-root e)]
             [(-->i (-var cs c) d)
              (define dom-E-root : (-dom → (℘ γ))
                (match-lambda
                  [(-dom _ ?xs d _) (set-subtract (E-root d) (if ?xs (list->set (map γ:lex ?xs)) ∅))]))
              (∪ (apply ∪ (if c (dom-E-root c) ∅) (map dom-E-root cs))
                 (if d (apply ∪ ∅ (map dom-E-root d)) ∅))]
             [(case--> cases) (apply ∪ ∅ (map E-root cases))]
             [E (log-debug "E-ROOT⟦~a⟧ = ∅~n" E) ∅]))))))
  )
