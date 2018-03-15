#lang typed/racket/base

(require (only-in racket/function curry)
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/match
         racket/list
         typed/racket/unit
         racket/splicing
         syntax/parse/define
         set-extras
         unreachable
         bnf
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide step@)

(define-unit step@
  (import val^ env^ sto^ evl^
          alloc^ app^ mon^ compile^
          proof-system^)
  (export step^)

  (: inj : (U -prog ⟦E⟧) → (Values Ξ Σ))
  (define (inj x)
    (define ⟦E⟧ (->⟦E⟧ x))
    (define αₖ₀ (αₖ ⟦E⟧ ⊥Ρ))
    (define Σ₀ (Σ ⊥Σᵥ ⊥Σₖ ⊥Σₐ))
    (values (⟦E⟧ ⊥Ρ {set ∅} (Ξ:co '() αₖ₀ H₀) Σ₀) Σ₀))

  (: ↝* : (U -prog ⟦E⟧) → (Values (℘ Blm) Σ))
  (define (↝* p)
    (define-values (Ξ₀ Σ) (inj p))
    ;; TODO real versioning
    (Ver . ≜ . (List Σᵥ Σₖ Σₐ))
    (define seen : (Mutable-HashTable Ξ:co Ver) (make-hash))
    (define (ver) : Ver (list (Σ-val Σ) (Σ-kon Σ) (Σ-evl Σ)))
    (define-set blms : Blm)
    
    (define db? (db:iter?))
    (define iter : Natural 0)
    (define cut? : (Natural → Boolean)
      (match (db:max-steps)
        [(? values n) (λ (i) (> i n))]
        [_ (λ _ #f)]))

    (let loop! ([front : (℘ Ξ) {set Ξ₀}])
      (set! iter (+ 1 iter))
      (when db?
        (printf "~a: ~a~n" iter (set-count front)))
      (unless (or (set-empty? front) (cut? iter))
        (loop!
         (for*/set : (℘ Ξ) ([Ξ₀ (in-set front)]
                            [Ξ₁ (in-set (↝ Ξ₀ Σ))]
                            #:unless (and (Blm? Ξ₁) (blms-add! Ξ₁))
                            [v₁ (in-value (ver))]
                            #:unless (equal? v₁ (hash-ref seen Ξ₁ #f)))
           (hash-set! seen Ξ₁ v₁)
           Ξ₁))))
    (values blms Σ)) 

  (: ->⟦E⟧ : (U -prog ⟦E⟧) → ⟦E⟧)
  (define (->⟦E⟧ x) (if (-prog? x) (↓ₚ x) x))

  (: ↝ : Ξ Σ → (℘ Ξ))
  (define (↝ Ξ Σ)
    (match Ξ
      [(Ξ:co K α H)
       (define R^₀ (Σₐ@ Σ Ξ))
       (cond
         [(set-empty? R^₀) ∅]
         [(match K
            [(cons F K*) (co R^₀ F (Ξ:co K* α H) Σ)]
            [_ (for/set : (℘ Ξ:co) ([Ξ₁ (in-set (Σₖ@ Σ α))])
                 (ret! R^₀ Ξ₁ Σ))])])]
      [_ ∅])) 

  (: co : R^ F Ξ:co Σ → (℘ Ξ))
  (define (co R^₀ F Ξ Σ)
    (match F
      [(F:Ap Vs ⟦E⟧s Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V^ Φ^)
           (define Vs* (cons V^ Vs))
           (match ⟦E⟧s
             [(cons ⟦E⟧ ⟦E⟧s*) {set (⟦E⟧ Ρ Φ^ (K+ (F:Ap Vs* ⟦E⟧s* Ρ ℓ) Ξ) Σ)}]
             [_ (match-define (cons fun args) (reverse Vs*))
                (app fun args ℓ Φ^ Ξ Σ)])))]
      [(F:Set! α)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R -void Φ^) Ξ Σ)}))]
      [(F:Let ℓ xs binds bounds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (define bounds*
             (for/fold ([acc : (Assoc Symbol V^) bounds])
                       ([x (in-list xs)] [V (in-list W)])
               (cons (cons x V) acc)))
           (match binds
             [(cons (cons xs* ⟦E⟧) binds*)
              {set (⟦E⟧ Ρ Φ^ (K+ (F:Let ℓ xs* binds* bounds* ⟦body⟧ Ρ) Ξ) Σ)}]
             ['()
              (define-values (xs Vs) (unzip bounds*))
              (define Ρ* (bind-args! Ρ xs Vs Φ^ H₀ Σ))
              {set (⟦body⟧ Ρ* Φ^ Ξ Σ)}])))]
      [(F:Letrec ℓ xs binds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (⊔ᵥ*! Σ (Ρ@* Ρ xs) W)
           {set (match binds
                  [(cons (cons xs* ⟦E⟧) binds*)
                   (⟦E⟧ Ρ Φ^ (K+ (F:Letrec ℓ xs* binds* ⟦body⟧ Ρ) Ξ) Σ)]
                  [_ (⟦body⟧ Ρ Φ^ Ξ Σ)])}))]
      [(F:If l ⟦E⟧₁ ⟦E⟧₂ Ρ)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (Φ^₁ Φ^₂) (plausible-splits Σ R^₀))
           (∪ (if (set-empty? Φ^₁) ∅ {set (⟦E⟧₁ Ρ Φ^₁ Ξ Σ)})
              (if (set-empty? Φ^₂) ∅ {set (⟦E⟧₂ Ρ Φ^₂ Ξ Σ)}))))]
      [(F:Bgn (cons ⟦E⟧ ⟦E⟧s) Ρ)
       (define-values (_ Φ^) (collapse-R^ R^₀))
       (define Ξ* (if (pair? ⟦E⟧s) (K+ (F:Bgn ⟦E⟧s Ρ) Ξ) Ξ))
       {set (⟦E⟧ Ρ Φ^ Ξ* Σ)}]
      [(F:Bgn0:V (cons ⟦E⟧ ⟦E⟧s) Ρ)
       (define-values (W^ Φ^) (collapse-R^ R^₀))
       (define Ξ* (if (pair? ⟦E⟧s) (K+ (F:Bgn0:E W^ ⟦E⟧s Ρ) Ξ) Ξ))
       {set (⟦E⟧ Ρ Φ^ Ξ* Σ)}]
      [(F:Bgn0:E W^ ⟦E⟧s Ρ)
       (define-values (_ Φ^) (collapse-R^ R^₀))
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*) (⟦E⟧ Ρ Φ^ (K+ (F:Bgn0:E W^ ⟦E⟧s* Ρ) Ξ) Σ)]
              [_ (ret! (R W^ Φ^) Ξ Σ)])}]
      [(F:Mon:C Ctx Ctc)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Val Φ^)
           (match Ctc
             [(cons ⟦C⟧ Ρ) {set (⟦C⟧ Ρ Φ^ (K+ (F:Mon:V Ctx Val) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon:V Ctx Val)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Ctc Φ^)
           (match Val
             [(cons ⟦V⟧ Ρ) {set (⟦V⟧ Ρ Φ^ (K+ (F:Mon:C Ctx Ctc) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon*:C Ctx rngs)
       (case rngs
         [(any) {set (ret! R^₀ Ξ Σ)}]
         [else
          (with-guarded-arity/collapse R^₀ (length rngs) (Ctx-loc Ctx)
            (λ (W Φ^)
              (define-values (βs ℓs) (unzip-by αℓ-_0 αℓ-_1 rngs))
              (match* ((Σᵥ@* Σ βs) W ℓs)
                [((cons C₁ Cs) (cons V₁ Vs) (cons ℓ₁ ℓs))
                 (define Ξ* (K+ (F:Mon* Ctx Cs Vs ℓs '()) Ξ))
                 (mon C₁ V₁ (Ctx-with-ℓ Ctx ℓ₁) Φ^ Ξ* Σ)]
                [('() '() '())
                 {set (ret! (W->R '() Φ^) Ξ Σ)}])))])]
      [(F:Mon* Ctx Cs Vs ℓs Res-rev)
       (define-values (W^ Φ^) (collapse-R^ R^₀))
       (match-define (list V^) (collapse-value-lists W^ 1))
       (define Res-rev* (cons V^ Res-rev))
       (match* (Cs Vs ℓs)
         [((cons C Cs) (cons V Vs) (cons ℓ ℓs))
          (define Ξ* (K+ (F:Mon* Ctx Cs Vs ℓs Res-rev*) Ξ))
          (mon C V (Ctx-with-ℓ Ctx ℓ) Φ^ Ξ* Σ)]
         [('() '() '())
          {set (ret! (W->R (reverse Res-rev*) Φ^) Ξ Σ)}])]
      [(F:Μ/C x)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (C-body Φ^)
           (define α (mk-α (-α:x/c x H₀)))
           (⊔ᵥ! Σ α C-body)
           {set (ret! (V->R (X/C α) Φ^) Ξ Σ)}))]
      [(F:==>:Dom inits↓ inits↑ ?rst rng Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V Φ^)
           (define inits↓* (cons V inits↓))
           {set (match inits↑
                  [(cons ⟦C⟧ ⟦C⟧s)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>:Dom inits↓* ⟦C⟧s ?rst rng Ρ ℓ) Ξ) Σ)]
                  [_ (if ?rst
                         (?rst Ρ Φ^ (K+ (F:==>:Rst inits↓* rng Ρ ℓ) Ξ) Σ)
                         (rng Ρ Φ^ (K+ (F:==>:Rng inits↓* #f ℓ) Ξ) Σ))])}))]
      [(F:==>:Rst inits rng Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (Vᵣ Φ^)
           {set (rng Ρ Φ^ (K+ (F:==>:Rng inits Vᵣ ℓ) Ξ) Σ)}))]
      [(F:==>:Rng inits ?rst ℓ)
       (define-values (D^ Φ^) (collapse-R^ R^₀))
       (define V (mk-==>! Σ H₀ inits ?rst D^ ℓ))
       {set (ret! (V->R V Φ^) Ξ Σ)}]
      [(F:==>i Ρ doms↓ dom-ctx doms↑) ???]
      [(F:St/C ℓ 𝒾 Cs ⟦C⟧s Ρ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define Cs* (cons C^ Cs))
           {set (match ⟦C⟧s
                  [(cons ⟦C⟧ ⟦C⟧s*)
                   (⟦C⟧ Ρ Φ^ (K+ (F:St/C ℓ 𝒾 Cs* ⟦C⟧s* Ρ) Ξ) Σ)]
                  [_
                   (define flds (mk-αℓ*! Σ (-𝒾-name 𝒾) (curry -α:struct/c 𝒾) H₀ ℓ (reverse Cs*)))
                   (define flat? (andmap C^-flat? Cs*))
                   (ret! (V->R (St/C flat? 𝒾 flds) Φ^) Ξ Σ)])}))]
      [(F:Def l lhs)
       (with-guarded-arity/collapse R^₀ (length lhs) +ℓ₀ ; TODO
         (λ (W Φ^)
           (⊔ᵥ*! Σ lhs W)
           {set (ret! (V->R -void Φ^) Ξ Σ)}))]
      [(F:Dec ℓ 𝒾)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define l (-𝒾-src 𝒾))
           (define α  (mk-α (-α:top 𝒾)))
           (define α* (mk-α (-α:wrp 𝒾)))
           (define V^ (Σᵥ@ Σ α))
           (mon C^ V^ (Ctx l 'dummy- l ℓ) Φ^ (K+ (F:Def l (list α*)) Ξ) Σ)))]
      [(K.Hv HV-Tag) ???]
      
      ;; Specific helpers
      [(F:Wrap G Ctx α)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R (X/G Ctx G α) Φ^) Ξ Σ)}))]
      [(F:Mon-Or/C Ctx Cₗ Cᵣ V) ???]
      [(F:If:Flat/C V^ Blm)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (Φ^₁ Φ^₂) (plausible-splits Σ R^₀))
           ???))]
      #;[(F:Fc-And/C -l ℓ V^ V^) ???]
      #;[(F:Fc-Or/C -l ℓ V^ V^ V^) ???]
      #;[(F:Fc-Not/C V^) ???]
      #;[(F:Fc-Struct/C l ℓ 𝒾 (Listof V^) (Listof ⟦E⟧) Ρ) ???]
      #;[(F:Fc:V -l ℓ ⟦E⟧ Ρ) ???]
      [(F:Hash-Set-Inner ℓ α) ???]
      [(F:Set-Add-Inner ℓ α) ???]
      [(F:Maybe-Havoc-Prim-Args ℓ Symbol) ???]
      #;[(F:Make-Prim-Range Ctx (Option (Listof αℓ)) (Listof V^) (Listof (List (Listof V) (Option V) (Listof V)))) ???]
      [(F:Implement-Predicate p) ???]
      [(F:Absurd) ∅])
    #;(match K₀
      ))

  (: ret! : (U R R^) Ξ:co Σ → Ξ:co)
  (define (ret! R Ξ Σ) (⊔ₐ! Σ Ξ R) Ξ)

  (: with-guarded-arity : R^ Natural ℓ (R^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-arity R^ n ℓ exec)
    (define-values (R^-goods W-bads) (filter/arity R^ n))
    (define blms (for/set : (℘ Blm) ([W (in-set W-bads)])
                   (Blm ℓ 'Λ (list 'arity (-b n)) W)))
    (∪ blms (if (set-empty? R^-goods) ∅ (exec R^-goods))))
  
  (: with-guarded-arity/collapse : R^ Natural ℓ (W Φ^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-arity/collapse R^ n ℓ exec)
    (with-guarded-arity R^ n ℓ
      (λ (R^-goods)
        (define-values (W-goods Φ-goods) (collapse-R^ R^-goods))
        (exec (collapse-value-lists W-goods n) Φ-goods))))

  (: with-guarded-single-arity/collapse : R^ ℓ (V^ Φ^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-single-arity/collapse R^ ℓ exec)
    (with-guarded-arity/collapse R^ 1 ℓ (λ (W Φ^) (exec (car W) Φ^))))

  (: mk-==>! : Σ H W (Option V^) W^ ℓ → V^)
  (define (mk-==>! Σ H doms-rev rst rngs ℓ)
    ???
    #|
    (define Dom
      (let ([Init (mk-αℓ*! 'dom -α:dom H ℓ (reverse doms-rev))])
        (cond [rst (define αᵣ (mk-α (-α:rst ℓ H)))
                   (define ℓᵣ (ℓ-with-id ℓ 'rest))
                   (-var Init (αℓ αᵣ ℓᵣ))]
              [else Init])))
    (define Rng^ ; Should have had special `any` contract
      (for/union : (℘ (Option W)) ([rng (in-set rngs)])
        (match rng
          [(list V^)
           #:when (∋ s 'any)
           ???])))
    |#
    #|
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
    (values (-=> Dom Rng) φ₂)
    |#)

  (: K+/And : -l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)
  (define (K+/And l ⟦E⟧s Ρ Ξ)
    (match ⟦E⟧s
      [(cons ⟦E⟧ ⟦E⟧s) (K+ (F:If l ⟦E⟧ (mk-V -ff) Ρ) (K+/And l ⟦E⟧s Ρ Ξ))]
      [_ Ξ]))

  (: K+/Or : -l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)
  (define (K+/Or l ⟦E⟧s Ρ Ξ)
    (match ⟦E⟧s
      [(cons ⟦E⟧ ⟦E⟧s) (K+ (F:If l (mk-V -tt) ⟦E⟧ Ρ) (K+/Or l ⟦E⟧s Ρ Ξ))]
      [_ Ξ]))

  (: mk-αℓ*! : Σ Symbol (ℓ H Index → -α) H ℓ (Listof V^) → (Listof αℓ))
  (define (mk-αℓ*! Σ tag mk H ℓ Vs)
    (for/list ([V (in-list Vs)] [i (in-naturals)] #:when (index? i))
      (define α (mk-α (mk ℓ H i)))
      (⊔ᵥ! Σ α V)
      (αℓ α (ℓ-with-id ℓ (cons tag i)))))

  (define db:iter? : (Parameterof Boolean) (make-parameter #f))
  (define db:max-steps : (Parameterof (Option Integer)) (make-parameter #f))
  )
