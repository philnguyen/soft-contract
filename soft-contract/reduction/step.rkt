#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function curry)
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/bool
         racket/match
         racket/list
         typed/racket/unit
         racket/splicing
         syntax/parse/define
         set-extras
         unreachable
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
          alloc^ app^ mon^
          proof-system^)
  (export step^)

  (: ↝! : Ξ Σ → (℘ Ξ))
  (define (↝! Ξ Σ)
    (match Ξ
      [(Ξ:co K₀ H₀)
       (define R^₀ (Σₐ@ Σ K₀))
       (if (set-empty? R^₀) ∅ (co R^₀ K₀ H₀ Σ))]
      [_ ∅])) 

  (: co : R^ K H Σ → (℘ Ξ))
  (define (co R^₀ K₀ H₀ Σ) 
    (match K₀
      [(K:Rt αₖ)
       (for/set : (℘ Ξ) ([Rt* (in-set (Σₖ@ Σ αₖ))])
         (match-define (Rt H K) Rt*)
         (ret! R^₀ K H Σ))]
      [(K:Ap Vs ⟦E⟧s Ρ ℓ K)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V^ Φ^)
           (define Vs* (cons V^ Vs))
           (match ⟦E⟧s
             [(cons ⟦E⟧ ⟦E⟧s*) {set (⟦E⟧ Ρ Φ^ (K:Ap Vs* ⟦E⟧s* Ρ ℓ K) H₀ Σ)}]
             [_ (match-define (cons fun args) (reverse Vs*))
                (app fun args ℓ Φ^ K H₀ Σ)])))]
      [(K:Set! α K)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R -void Φ^) K H₀ Σ)}))]
      [(K:Let ℓ xs binds bounds ⟦body⟧ Ρ K)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (define bounds*
             (for/fold ([acc : (Assoc Symbol V^) bounds])
                       ([x (in-list xs)] [V (in-list W)])
               (cons (cons x V) acc)))
           (match binds
             [(cons (cons xs* ⟦E⟧) binds*)
              {set (⟦E⟧ Ρ Φ^ (K:Let ℓ xs* binds* bounds* ⟦body⟧ Ρ K) H₀ Σ)}]
             ['()
              (define-values (xs Vs) (unzip bounds*))
              (define Ρ* (bind-args! Ρ xs Vs ℓ Φ^ H₀ Σ))
              {set (⟦body⟧ Ρ* Φ^ K H₀ Σ)}])))]
      [(K:Letrec ℓ xs binds ⟦body⟧ Ρ K)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (⊔ᵥ*! Σ (Ρ@* Ρ xs) W)
           {set (match binds
                  [(cons (cons xs* ⟦E⟧) binds*)
                   (⟦E⟧ Ρ Φ^ (K:Letrec ℓ xs* binds* ⟦body⟧ Ρ K) H₀ Σ)]
                  [_ (⟦body⟧ Ρ Φ^ K H₀ Σ)])}))]
      [(K:If l ⟦E⟧₁ ⟦E⟧₂ Ρ K)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (R^₁ R^₂) (plausible-splits Σ R^₀))
           (define (t) (⟦E⟧₁ Ρ (collapse-R^/Φ^ R^₁) K H₀ Σ))
           (define (f) (⟦E⟧₂ Ρ (collapse-R^/Φ^ R^₂) K H₀ Σ))
           (cond [(set-empty? R^₁) {set (f)}]
                 [(set-empty? R^₂) {set (t)}]
                 [else {set (t) (f)}])))]
      [(K:Bgn ⟦E⟧s Ρ K)
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*)
               (define-values (_ Φ^) (collapse-R^ R^₀))
               (⟦E⟧ Ρ Φ^ (K:Bgn ⟦E⟧s* Ρ K) H₀ Σ)]
              [_ (ret! R^₀ K H₀ Σ)])}]
      [(K:Bgn0:V ⟦E⟧s Ρ K)
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*)
               (define-values (W^ Φ^) (collapse-R^ R^₀))
               (⟦E⟧ Ρ Φ^ (K:Bgn0:E W^ ⟦E⟧s Ρ K) H₀ Σ)]
              [_ (ret! R^₀ K H₀ Σ)])}]
      [(K:Bgn0:E W^ ⟦E⟧s Ρ K)
       (define-values (_ Φ^) (collapse-R^ R^₀))
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*) (⟦E⟧ Ρ Φ^ (K:Bgn0:E W^ ⟦E⟧s* Ρ K) H₀ Σ)]
              [_ (ret! (R W^ Φ^) K H₀ Σ)])}]
      [(K:Mon:C Ctx Ctc K)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Val Φ^)
           (match Ctc
             [(cons ⟦C⟧ Ρ) {set (⟦C⟧ Ρ Φ^ (K:Mon:V Ctx Val K) H₀ Σ)}]
             [(? set?) (mon Ctx Ctc Val H₀ Φ^ Σ K)])))]
      [(K:Mon:V Ctx Val K)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Ctc Φ^)
           (match Val
             [(cons ⟦V⟧ Ρ) {set (⟦V⟧ Ρ Φ^ (K:Mon:C Ctx Ctc K) H₀ Σ)}]
             [(? set?) (mon Ctx Ctc Val H₀ Φ^ Σ K)])))]
      [(K:Mon*:C Ctx rngs K)
       (case rngs
         [(any) {set (ret! R^₀ K H₀ Σ)}]
         [else
          (with-guarded-arity/collapse R^₀ (length rngs) (Ctx-loc Ctx)
            (λ (W Φ^)
              (define-values (βs ℓs) (unzip-by αℓ-_0 αℓ-_1 rngs))
              (match* ((Σᵥ@* Σ βs) W ℓs)
                [((cons C₁ Cs) (cons V₁ Vs) (cons ℓ₁ ℓs))
                 (mon (Ctx-with-ℓ Ctx ℓ₁) C₁ V₁ H₀ Φ^ Σ (K:Mon* Ctx Cs Vs ℓs '() K))]
                [('() '() '())
                 {set (ret! (W->R '() Φ^) K H₀ Σ)}])))])]
      [(K:Mon* Ctx Cs Vs ℓs Res-rev K)
       (define-values (W^ Φ^) (collapse-R^ R^₀))
       (match-define (list V^) (collapse-value-lists W^ 1))
       (define Res-rev* (cons V^ Res-rev))
       (match* (Cs Vs ℓs)
         [((cons C Cs) (cons V Vs) (cons ℓ ℓs))
          (mon (Ctx-with-ℓ Ctx ℓ) C V H₀ Φ^ Σ (K:Mon* Ctx Cs Vs ℓs Res-rev* K))]
         [('() '() '())
          {set (ret! (W->R (reverse Res-rev*) Φ^) K H₀ Σ)}])]
      [(K:Μ/C x K)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (C-body Φ^)
           (define α (mk-α (-α:x/c x H₀)))
           (⊔ᵥ! Σ α C-body)
           {set (ret! (V->R (X/C α) Φ^) K H₀ Σ)}))]
      [(K:==>:Dom inits↓ inits↑ ?rst rng Ρ ℓ K)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V Φ^)
           (define inits↓* (cons V inits↓))
           {set (match inits↑
                  [(cons ⟦C⟧ ⟦C⟧s)
                   (⟦C⟧ Ρ Φ^ (K:==>:Dom inits↓* ⟦C⟧s ?rst rng Ρ ℓ K) H₀ Σ)]
                  [_ (if ?rst
                         (?rst Ρ Φ^ (K:==>:Rst inits↓* rng Ρ ℓ K) H₀ Σ)
                         (rng Ρ Φ^ (K:==>:Rng inits↓* #f ℓ K) H₀ Σ))])}))]
      [(K:==>:Rst inits rng Ρ ℓ K)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (Vᵣ Φ^)
           {set (rng Ρ Φ^ (K:==>:Rng inits Vᵣ ℓ K) H₀ Σ)}))]
      [(K:==>:Rng inits ?rst ℓ K)
       (define-values (D^ Φ^) (collapse-R^ R^₀))
       (define V (mk-==>! Σ H₀ inits ?rst D^ ℓ))
       {set (ret! (V->R V Φ^) K H₀ Σ)}]
      [(K:==>i Ρ doms↓ dom-ctx doms↑ K) ???]
      [(K:St/C ℓ 𝒾 Cs ⟦C⟧s Ρ K)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define Cs* (cons C^ Cs))
           {set (match ⟦C⟧s
                  [(cons ⟦C⟧ ⟦C⟧s*)
                   (⟦C⟧ Ρ Φ^ (K:St/C ℓ 𝒾 Cs* ⟦C⟧s* Ρ K) H₀ Σ)]
                  [_
                   (define flds (mk-αℓ*! Σ (-𝒾-name 𝒾) (curry -α:struct/c 𝒾) H₀ ℓ (reverse Cs*)))
                   (define flat? (andmap C^-flat? Cs*))
                   (ret! (V->R (St/C flat? 𝒾 flds) Φ^) K H₀ Σ)])}))]
      [(K:Def l lhs K)
       (with-guarded-arity/collapse R^₀ (length lhs) +ℓ₀ ; TODO
         (λ (W Φ^)
           (⊔ᵥ*! Σ lhs W)
           {set (ret! (V->R -void Φ^) K H₀ Σ)}))]
      [(K:Dec ℓ 𝒾 K)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define l (-𝒾-src 𝒾))
           (define α  (mk-α (-α:top 𝒾)))
           (define α* (mk-α (-α:wrp 𝒾)))
           (define V^ (Σᵥ@ Σ α))
           (mon (Ctx l 'dummy- l ℓ) C^ V^ H₀ Φ^ Σ (K:Def l (list α*) K))))]
      [(K.Hv HV-Tag K) ???]
      
      ;; Specific helpers
      [(K:Wrap G Ctx α K)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R (X/G Ctx G α) Φ^) K H₀ Σ)}))]
      [(K:Mon-Or/C Ctx Cₗ Cᵣ V K) ???]
      [(K:If:Flat/C V^ Blm K)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (R^₁ R^₂) (plausible-splits Σ R^₀))
           ???))]
      #;[(K:Fc-And/C -l ℓ V^ V^ K) ???]
      #;[(K:Fc-Or/C -l ℓ V^ V^ V^ K) ???]
      #;[(K:Fc-Not/C V^ K) ???]
      #;[(K:Fc-Struct/C l ℓ 𝒾 (Listof V^) (Listof ⟦E⟧) Ρ K) ???]
      #;[(K:Fc:V -l ℓ ⟦E⟧ Ρ K) ???]
      [(K:Hash-Set-Inner ℓ α K) ???]
      [(K:Set-Add-Inner ℓ α K) ???]
      [(K:Maybe-Havoc-Prim-Args ℓ Symbol K) ???]
      #;[(K:Make-Prim-Range Ctx (Option (Listof αℓ)) (Listof V^) (Listof (List (Listof V) (Option V) (Listof V))) K) ???]
      [(K:Implement-Predicate p K) ???]
      [(K:Absurd) ∅]))

  (: ret! : (U R R^) K H Σ → Ξ:co)
  (define (ret! R K H Σ)
    (⊔ₐ! Σ K R)
    (Ξ:co K H))

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

  (: mk-αℓ*! : Σ Symbol (ℓ H Index → -α) H ℓ (Listof V^) → (Listof αℓ))
  (define (mk-αℓ*! Σ tag mk H ℓ Vs)
    (for/list ([V (in-list Vs)] [i (in-naturals)] #:when (index? i))
      (define α (mk-α (mk ℓ H i)))
      (⊔ᵥ! Σ α V)
      (αℓ α (ℓ-with-id ℓ (cons tag i)))))
  )
