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
  (define (↝! Ξ₀ Σ)
    (match Ξ₀
      [(Ξ:co (and K₀ (K Fs α)) H)
       (define R^₀ (Σₐ@ Σ K₀))
       (cond
         [(set-empty? R^₀) ∅]
         [(match Fs
            [(cons F Fs*) (co R^₀ F (K Fs* α) H Σ)]
            [_ (for/set : (℘ Ξ) ([Ξ₁ (in-set (Σₖ@ Σ α))])
                 (match-define (Ξ:co K₁ H₁) Ξ₁)
                 (ret! R^₀ K₁ H₁ Σ))])])]
      [_ ∅])) 

  (: co : R^ F K H Σ → (℘ Ξ))
  (define (co R^₀ F K H Σ)
    (match F
      [(F:Ap Vs ⟦E⟧s Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V^ Φ^)
           (define Vs* (cons V^ Vs))
           (match ⟦E⟧s
             [(cons ⟦E⟧ ⟦E⟧s*) {set (⟦E⟧ Ρ Φ^ (K+ (F:Ap Vs* ⟦E⟧s* Ρ ℓ) K) H₀ Σ)}]
             [_ (match-define (cons fun args) (reverse Vs*))
                (app fun args ℓ Φ^ K H₀ Σ)])))]
      [(F:Set! α)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R -void Φ^) K H₀ Σ)}))]
      [(F:Let ℓ xs binds bounds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (define bounds*
             (for/fold ([acc : (Assoc Symbol V^) bounds])
                       ([x (in-list xs)] [V (in-list W)])
               (cons (cons x V) acc)))
           (match binds
             [(cons (cons xs* ⟦E⟧) binds*)
              {set (⟦E⟧ Ρ Φ^ (K+ (F:Let ℓ xs* binds* bounds* ⟦body⟧ Ρ) K) H₀ Σ)}]
             ['()
              (define-values (xs Vs) (unzip bounds*))
              (define Ρ* (bind-args! Ρ xs Vs ℓ Φ^ H₀ Σ))
              {set (⟦body⟧ Ρ* Φ^ K H₀ Σ)}])))]
      [(F:Letrec ℓ xs binds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse R^₀ (length xs) ℓ
         (λ (W Φ^)
           (⊔ᵥ*! Σ (Ρ@* Ρ xs) W)
           {set (match binds
                  [(cons (cons xs* ⟦E⟧) binds*)
                   (⟦E⟧ Ρ Φ^ (K+ (F:Letrec ℓ xs* binds* ⟦body⟧ Ρ) K) H₀ Σ)]
                  [_ (⟦body⟧ Ρ Φ^ K H₀ Σ)])}))]
      [(F:If l ⟦E⟧₁ ⟦E⟧₂ Ρ)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (R^₁ R^₂) (plausible-splits Σ R^₀))
           (define (t) (⟦E⟧₁ Ρ (collapse-R^/Φ^ R^₁) K H₀ Σ))
           (define (f) (⟦E⟧₂ Ρ (collapse-R^/Φ^ R^₂) K H₀ Σ))
           (cond [(set-empty? R^₁) {set (f)}]
                 [(set-empty? R^₂) {set (t)}]
                 [else {set (t) (f)}])))]
      [(F:Bgn ⟦E⟧s Ρ)
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*)
               (define-values (_ Φ^) (collapse-R^ R^₀))
               (⟦E⟧ Ρ Φ^ (K+ (F:Bgn ⟦E⟧s* Ρ) K) H₀ Σ)]
              [_ (ret! R^₀ K H₀ Σ)])}]
      [(F:Bgn0:V ⟦E⟧s Ρ)
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*)
               (define-values (W^ Φ^) (collapse-R^ R^₀))
               (⟦E⟧ Ρ Φ^ (K+ (F:Bgn0:E W^ ⟦E⟧s Ρ) K) H₀ Σ)]
              [_ (ret! R^₀ K H₀ Σ)])}]
      [(F:Bgn0:E W^ ⟦E⟧s Ρ)
       (define-values (_ Φ^) (collapse-R^ R^₀))
       {set (match ⟦E⟧s
              [(cons ⟦E⟧ ⟦E⟧s*) (⟦E⟧ Ρ Φ^ (K+ (F:Bgn0:E W^ ⟦E⟧s* Ρ) K) H₀ Σ)]
              [_ (ret! (R W^ Φ^) K H₀ Σ)])}]
      [(F:Mon:C Ctx Ctc)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Val Φ^)
           (match Ctc
             [(cons ⟦C⟧ Ρ) {set (⟦C⟧ Ρ Φ^ (K+ (F:Mon:V Ctx Val) K) H₀ Σ)}]
             [(? set?) (mon Ctx Ctc Val H₀ Φ^ Σ K)])))]
      [(F:Mon:V Ctx Val)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Ctc Φ^)
           (match Val
             [(cons ⟦V⟧ Ρ) {set (⟦V⟧ Ρ Φ^ (K+ (F:Mon:C Ctx Ctc) K) H₀ Σ)}]
             [(? set?) (mon Ctx Ctc Val H₀ Φ^ Σ K)])))]
      [(F:Mon*:C Ctx rngs)
       (case rngs
         [(any) {set (ret! R^₀ K H₀ Σ)}]
         [else
          (with-guarded-arity/collapse R^₀ (length rngs) (Ctx-loc Ctx)
            (λ (W Φ^)
              (define-values (βs ℓs) (unzip-by αℓ-_0 αℓ-_1 rngs))
              (match* ((Σᵥ@* Σ βs) W ℓs)
                [((cons C₁ Cs) (cons V₁ Vs) (cons ℓ₁ ℓs))
                 (define K* (K+ (F:Mon* Ctx Cs Vs ℓs '()) K))
                 (mon (Ctx-with-ℓ Ctx ℓ₁) C₁ V₁ H₀ Φ^ Σ K*)]
                [('() '() '())
                 {set (ret! (W->R '() Φ^) K H₀ Σ)}])))])]
      [(F:Mon* Ctx Cs Vs ℓs Res-rev)
       (define-values (W^ Φ^) (collapse-R^ R^₀))
       (match-define (list V^) (collapse-value-lists W^ 1))
       (define Res-rev* (cons V^ Res-rev))
       (match* (Cs Vs ℓs)
         [((cons C Cs) (cons V Vs) (cons ℓ ℓs))
          (define K* (K+ (F:Mon* Ctx Cs Vs ℓs Res-rev*) K))
          (mon (Ctx-with-ℓ Ctx ℓ) C V H₀ Φ^ Σ K*)]
         [('() '() '())
          {set (ret! (W->R (reverse Res-rev*) Φ^) K H₀ Σ)}])]
      [(F:Μ/C x)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (C-body Φ^)
           (define α (mk-α (-α:x/c x H₀)))
           (⊔ᵥ! Σ α C-body)
           {set (ret! (V->R (X/C α) Φ^) K H₀ Σ)}))]
      [(F:==>:Dom inits↓ inits↑ ?rst rng Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V Φ^)
           (define inits↓* (cons V inits↓))
           {set (match inits↑
                  [(cons ⟦C⟧ ⟦C⟧s)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>:Dom inits↓* ⟦C⟧s ?rst rng Ρ ℓ) K) H₀ Σ)]
                  [_ (if ?rst
                         (?rst Ρ Φ^ (K+ (F:==>:Rst inits↓* rng Ρ ℓ) K) H₀ Σ)
                         (rng Ρ Φ^ (K+ (F:==>:Rng inits↓* #f ℓ) K) H₀ Σ))])}))]
      [(F:==>:Rst inits rng Ρ ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (Vᵣ Φ^)
           {set (rng Ρ Φ^ (K+ (F:==>:Rng inits Vᵣ ℓ) K) H₀ Σ)}))]
      [(F:==>:Rng inits ?rst ℓ)
       (define-values (D^ Φ^) (collapse-R^ R^₀))
       (define V (mk-==>! Σ H₀ inits ?rst D^ ℓ))
       {set (ret! (V->R V Φ^) K H₀ Σ)}]
      [(F:==>i Ρ doms↓ dom-ctx doms↑) ???]
      [(F:St/C ℓ 𝒾 Cs ⟦C⟧s Ρ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define Cs* (cons C^ Cs))
           {set (match ⟦C⟧s
                  [(cons ⟦C⟧ ⟦C⟧s*)
                   (⟦C⟧ Ρ Φ^ (K+ (F:St/C ℓ 𝒾 Cs* ⟦C⟧s* Ρ) K) H₀ Σ)]
                  [_
                   (define flds (mk-αℓ*! Σ (-𝒾-name 𝒾) (curry -α:struct/c 𝒾) H₀ ℓ (reverse Cs*)))
                   (define flat? (andmap C^-flat? Cs*))
                   (ret! (V->R (St/C flat? 𝒾 flds) Φ^) K H₀ Σ)])}))]
      [(F:Def l lhs)
       (with-guarded-arity/collapse R^₀ (length lhs) +ℓ₀ ; TODO
         (λ (W Φ^)
           (⊔ᵥ*! Σ lhs W)
           {set (ret! (V->R -void Φ^) K H₀ Σ)}))]
      [(F:Dec ℓ 𝒾)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define l (-𝒾-src 𝒾))
           (define α  (mk-α (-α:top 𝒾)))
           (define α* (mk-α (-α:wrp 𝒾)))
           (define V^ (Σᵥ@ Σ α))
           (mon (Ctx l 'dummy- l ℓ) C^ V^ H₀ Φ^ Σ (K+ (F:Def l (list α*)) K))))]
      [(K.Hv HV-Tag) ???]
      
      ;; Specific helpers
      [(F:Wrap G Ctx α)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R (X/G Ctx G α) Φ^) K H₀ Σ)}))]
      [(F:Mon-Or/C Ctx Cₗ Cᵣ V) ???]
      [(F:If:Flat/C V^ Blm)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (define-values (R^₁ R^₂) (plausible-splits Σ R^₀))
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
