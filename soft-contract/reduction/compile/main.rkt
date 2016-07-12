#lang typed/racket/base

(provide ↓ₑ)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "base.rkt"
         "kontinuation.rkt"
         racket/set
         racket/match)

(: ↓ₑ : -l -e → -⟦e⟧)
;; Compile expression to computation that returns next configurations and store deltas
(define (↓ₑ l e)

  (define (↓ [e : -e]) (↓ₑ l e))

  (remember-e!
   (match e
     [(-λ xs e*)
      (define ⟦e*⟧ (↓ e*))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (define s (canonicalize-e Γ e))
        (⟦k⟧ (-W (list (-Clo xs ⟦e*⟧ ρ Γ)) s) Γ 𝒞 σ M))]
     [(-case-λ clauses)
      (define ⟦clause⟧s : (Listof (Pairof (Listof Var-Name) -⟦e⟧))
        (for/list ([clause clauses])
          (match-define (cons xs e) clause)
          (cons xs (↓ e))))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (define s (canonicalize-e Γ e))
        (⟦k⟧ (-W (list (-Case-Clo ⟦clause⟧s ρ Γ)) s) Γ 𝒞 σ M))]
     [(? -prim? p) (↓ₚᵣₘ p)]
     [(-• i)
      (define W (-W -●/Vs e))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦k⟧ W Γ 𝒞 σ M))]
     [(-x x) (↓ₓ l x)]
     [(and 𝒾 (-𝒾 x l₀))

      (: V->s : -σ -V → -s)
      (define (V->s σ V) 
        (with-debugging/off
          ((ans)
           (match V
             [(? -o? o) o]
             [(-Ar _ (? -o? o) _) o]
             [(-Ar _ (and α (or (? -α.def?) (? -α.wrp?) (? -e?))) _)
              (match (hash-ref σ α)
                [(? set? s) #:when (= 1 (set-count s)) (V->s σ (set-first s))]
                [_ #f])]
             [(-Clo xs ⟦e⟧ ρ _) #:when (ρ-empty? ρ)
              (cond [(recall-e ⟦e⟧) => (λ ([e : -e]) (-λ xs e))] ; hack
                    [else #f])]
             [(-St s αs) (apply -?@ (-st-mk s) (αs->ss αs))]
             [(-St/C _ s αs) (-?struct/c s (αs->ss αs))]
             [(-And/C _ αₗ αᵣ) (-?@ 'and/c (α->s αₗ) (α->s αᵣ))]
             [(-Or/C  _ αₗ αᵣ) (-?@ 'or/c  (α->s αₗ) (α->s αᵣ))]
             [(-Not/C α) (-?@ 'not/c (α->s α))]
             [(-Vector/C αs) (apply -?@ 'vector/c (αs->ss αs))]
             [(-Vectorof α) (-?@ 'vectorof (α->s α))]
             [(-x/C (-α.x/c ℓ)) (-x/c ℓ)]
             [_ #f]))
          (printf "V->s: ~a ↦ ~a~n" V ans)))

      (cond
        ;; same-module referencing returns unwrapped version
        [(equal? l₀ l)
         (define α (-α.def 𝒾))
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (define-values (Vs old?) (σ@ σ α))
           (define ?𝒾 (and old? 𝒾))
           (for*/ans ([V Vs])
             (define s (or (V->s σ V) ?𝒾))
             (⟦k⟧ (-W (list V) s) Γ 𝒞 σ M)))]
        ;; cross-module referencing returns wrapped version
        ;; and (HACK) supplies the negative monitoring context
        [else
         (define α (-α.wrp 𝒾))
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (define-values (Vs old?) (σ@ σ α))
           (define ?𝒾 (and old? 𝒾))
           (for*/ans ([V Vs])
             (define s (or (V->s σ V) ?𝒾))
             (⟦k⟧ (-W (list (supply-negative-party l V)) s) Γ 𝒞 σ M)))])]
     [(-@ f xs ℓ)
      (define ⟦f⟧  (↓ f))
      (define ⟦x⟧s (map ↓ xs))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦f⟧ ρ Γ 𝒞 σ M (ap∷ '() ⟦x⟧s ρ l ℓ ⟦k⟧)))]
     [(-if e₀ e₁ e₂)
      (define ⟦e₀⟧ (↓ e₀))
      (define ⟦e₁⟧ (↓ e₁))
      (define ⟦e₂⟧ (↓ e₂))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦e₀⟧ ρ Γ 𝒞 σ M (if∷ l ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
     [(-wcm k v b) (error '↓ₑ "TODO: wcm")]
     [(-begin es)
      (match (map ↓ es)
        ['()
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (⟦k⟧ -Void/W Γ 𝒞 σ M))]
        [(cons ⟦e⟧ ⟦e⟧s)
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (⟦e⟧ ρ Γ 𝒞 σ M (bgn∷ ⟦e⟧s ρ ⟦k⟧)))])]
     [(-begin0 e₀ es)
      (define ⟦e₀⟧ (↓ e₀))
      (define ⟦e⟧s (map ↓ es))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦e₀⟧ ρ Γ 𝒞 σ M (bgn0.v∷ ⟦e⟧s ρ ⟦k⟧)))]
     [(-quote q)
      (cond
        [(Base? q)
         (define b (-b q))
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (⟦k⟧ (-W (list b) b) Γ 𝒞 σ M))]
        [else (error '↓ₑ "TODO: (quote ~a)" q)])]
     [(-let-values bnds e*)
      (define ⟦bnd⟧s
        (for/list : (Listof (Pairof (Listof Var-Name) -⟦e⟧)) ([bnd bnds])
          (match-define (cons xs eₓₛ) bnd)
          (cons xs (↓ eₓₛ))))
      (define ⟦e*⟧ (↓ e*))
      (match ⟦bnd⟧s
        ['() ⟦e*⟧]
        [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (⟦e⟧ₓₛ ρ Γ 𝒞 σ M (let∷ l xs ⟦bnd⟧s* '() ⟦e*⟧ ρ ⟦k⟧)))])]
     [(-letrec-values bnds e*)
      (define ⟦bnd⟧s
        (for/list : (Listof (Pairof (Listof Var-Name) -⟦e⟧)) ([bnd bnds])
          (match-define (cons xs eₓₛ) bnd)
          (cons xs (↓ eₓₛ))))
      (define ⟦e*⟧ (↓ e*))
      (match ⟦bnd⟧s
        ['() ⟦e*⟧]
        [(cons (cons xs ⟦e⟧ₓₛ) ⟦bnd⟧s*)
         (λ (ρ Γ 𝒞 σ M ⟦k⟧)
           (define-values (ρ* σ* δσ)
             (for*/fold ([ρ  : -ρ  ρ]
                         [σ  : -σ  σ]
                         [δσ : -Δσ ⊥σ])
                        ([⟦bnd⟧ ⟦bnd⟧s]
                         [xs (in-value (car ⟦bnd⟧))]
                         [x xs])
               (define α (-α.x x 𝒞))
               (values (ρ+ ρ x α)
                       (σ⊔ σ  α 'undefined #t)
                       (σ⊔ ⊥σ α 'undefined #t))))
           (define-values (ςs δσ₀ δσₖ δM)
             (⟦e⟧ₓₛ ρ* Γ 𝒞 σ* M (letrec∷ l xs ⟦bnd⟧s* ⟦e*⟧ ρ* ⟦k⟧)))
           (values ςs (⊔σ δσ₀ δσ) δσₖ δM))])]
     [(-set! x e*)
      (define ⟦e*⟧ (↓ e*))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦e*⟧ ρ Γ 𝒞 σ M (set!∷ (ρ@ ρ x) ⟦k⟧)))]
     [(-error msg)
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦k⟧ (-blm l 'Λ '() (list (-b msg))) Γ 𝒞 σ M))]
     [(-amb es)
      (define ⟦e⟧s (set-map es ↓))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (for*/ans ([⟦e⟧ ⟦e⟧s]) (⟦e⟧ ρ Γ 𝒞 σ M ⟦k⟧)))]
     [(-μ/c x c)
      (define ⟦c⟧ (↓ c))
      (λ (ρ Γ 𝒞 σ M ⟦k⟧)
        (⟦c⟧ ρ Γ 𝒞 σ M (μ/c∷ l x ⟦k⟧)))]
     [(--> cs d ℓ) (error '↓ₑ "TODO: -->")]
     [(-->i cs (and mk-d (-λ xs d)) ℓ) (error '↓ₑ "TODO: -->i")]
     [(-case-> clauses ℓ)
      (error '↓ₑ "TODO: case->")]
     [(-x/c x)
      (error '↓ₑ "TODO: x/c")]
     [(-struct/c si cs l)
      (error '↓ₑ "TODO: struct/c")]
     [_
      (error '↓ₑ "unhandled: ~a" (show-e e))]
     )
   e))

