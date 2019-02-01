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
          exec^)
  (export gc^)

  (: gc : (℘ T) Σ → Σ)
  (define (gc root Σ₀)
    (define seen : (Mutable-HashTable T #t) (make-hash))

    (: touch : T Σ → Σ)
    (define (touch T Σ)
      (if (and (hash-has-key? Σ₀ T) (not (hash-has-key? seen T)))
          (match-let ([(and r (cons Vs _)) (hash-ref Σ₀ T)])
            (hash-set! seen T #t)
            (foldl touch* (hash-set Σ T r) (set-map Vs V-root)))
          Σ))
    
    (: touch* : (℘ T) Σ → Σ)
    (define (touch* Ts Σ) (set-fold touch Σ Ts))

    #;(let ([Σ* (touch* root ⊥Σ)])
      ;; Try to re-use old instance
        (if (= (hash-count Σ*) (hash-count Σ₀)) Σ₀ Σ*))
    ;; FIXME!!!
    Σ₀)

  (define V-root : (V → (℘ (U α T:@)))
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
      [(Seal/C α) {set α}]
      [(St/C _ αs _) (list->set αs)]
      [(Vectof/C α _) {set α}]
      [(Vect/C αs _) (list->set αs)]
      [(Hash/C αₖ αᵥ _) {set αₖ αᵥ}]
      [(Set/C α _) {set α}]
      [(? ==>? V) (==>-root V)]
      [(==>i doms rng) (apply ∪ (Dom-root rng) (map Dom-root doms))]
      [(∀/C _ _ Ρ) Ρ]
      [(Case-=> Cs) (apply ∪ ∅ (map ==>-root Cs))]
      [(? α? α) {set α}]
      [(? T:@? T) (define ans (T-root T))
                  (printf "root ~a = ~a~n" T (T-root T))
                  ans]
      [(or (? -prim?) (? -●?)) ∅]))

  (: T-root : T → (℘ (U T:@ α)))
  (define T-root
    (match-lambda
      [(and T (T:@ _ Ts)) (apply ∪ {set T} (map T-root Ts))]
      [(? α? α) {set α}]
      [_ ∅]))

  (: V^-root : V^ → (℘ (U T:@ α)))
  (define (V^-root Vs) (set-union-map V-root Vs))

  (: W-root : W → (℘ (U T:@ α)))
  (define (W-root W) (apply ∪ ∅ (map V^-root W)))

  (define ==>-root : (==> → (℘ (U T:@ α)))
    (match-lambda
      [(==> (-var dom:init ?dom:rest) rng _)
       (∪ (list->set dom:init)
          (if ?dom:rest {set ?dom:rest} ∅)
          (if rng (list->set rng) ∅))]))

  (define Dom-root : (Dom → (℘ (U T:@ α)))
    (match-lambda [(Dom _ C _) (if (Clo? C) (Clo-_2 C) {set C})]))

  (: E-root : E → (℘ γ))
  ;; Compute free variables for expression. Return set of variable names.
  (define E-root
    (match-lambda
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
      [(--> (-var cs c) d _) (apply ∪ (if c (E-root c) ∅) (E-root d) (map E-root cs))]
      [(-->i cs d)
       (define dom-E-root : (-dom → (℘ γ))
         (match-lambda
           [(-dom _ ?xs d _) (set-subtract (E-root d) (if ?xs (list->set (map γ:lex ?xs)) ∅))]))
       (apply ∪ (dom-E-root d) (map dom-E-root cs))]
      [(case--> cases) (apply ∪ ∅ (map E-root cases))]
      [E (log-debug "E-ROOT⟦~a⟧ = ∅~n" E) ∅]))

  )
