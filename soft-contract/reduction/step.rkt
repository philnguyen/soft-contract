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
  (import static-info^
          val^ env^ sto^ evl^
          prover^
          prims^
          alloc^ app^ mon^ fc^ compile^ havoc^)
  (export step^)

  (: inj : (U -prog ⟦E⟧) → (Values Ξ Σ))
  (define (inj x)
    (define ⟦E⟧ (->⟦E⟧ x))
    (define αₖ₀ (αₖ ⟦E⟧ ⊥Ρ))
    (define Σ₀ (Σ ⊥Σᵥ ⊥Σₖ ⊥Σₐ))
    (values (⟦E⟧ ⊥Ρ ⊥Φ^ (Ξ:co (K '() αₖ₀) #f H₀) Σ₀) Σ₀))

  (: ↝* : (U -prog ⟦E⟧) → (Values (℘ Blm) Σ))
  (define (↝* p)
    (define-values (Ξ₀ Σ) (inj p))
    ;; TODO real versioning
    (Ver . ≜ . (List Σᵥ Σₖ Σₐ))
    (define seen : (Mutable-HashTable Ξ:co Ver) (make-hash))
    (define (ver) : Ver (list (Σ-val Σ) (Σ-kon Σ) (Σ-evl Σ)))
    (define-set blms : Blm)
    
    (define db? (db:iter?))
    (define cut? : (Natural → Boolean)
      (match (db:max-steps)
        [(? values n) (λ (i) (> i n))]
        [_ (λ _ #f)]))

    (let loop! ([front : (℘ Ξ) {set Ξ₀}] [iter : Natural 0])
      (unless (or (set-empty? front) (cut? iter))
        (when db?
          (printf "~a: ~a~n" iter (set-count front)))
        (loop!
         (for*/set : (℘ Ξ) ([Ξ₀ (in-set front)]
                            [Ξ₁ (in-set (↝ Ξ₀ Σ))]
                            #:unless (and (Blm? Ξ₁) (blms-add! Ξ₁))
                            [v₁ (in-value (ver))]
                            #:unless (equal? v₁ (hash-ref seen Ξ₁ #f)))
           (hash-set! seen Ξ₁ v₁)
           Ξ₁)
         (add1 iter))))
    (values blms Σ)) 

  (: ->⟦E⟧ : (U -prog ⟦E⟧) → ⟦E⟧)
  (define (->⟦E⟧ x) (if (-prog? x) (↓ₚ x) x))

  (: ↝ : Ξ Σ → (℘ Ξ))
  (define (↝ Ξ Σ)
    (match Ξ
      [(Ξ:co (K Fs α) M H)
       (define R^₀ (Σₐ@ Σ Ξ))
       (cond
         [(set-empty? R^₀) ∅]
         [(match Fs
            [(cons F Fs*) (co R^₀ F (Ξ:co (K Fs* α) M H) Σ)]
            ['()
             (∪ (for/set : (℘ Ξ:co) ([Ξ₁ (in-set (Σₖ@ Σ α))])
                  (ret! R^₀ Ξ₁ Σ))
                (match α ; special address denoting havoc
                  [(cons (? pair? tag) _) (havoc tag R^₀ Ξ Σ)]
                  [_ ∅]))])])]
      [_ ∅])) 

  (: co : R^ F Ξ:co Σ → (℘ Ξ))
  (define (co R^₀ F Ξ Σ)
    (match F
      [(F:Ap Vs args ℓ)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V^ Φ^)
           (define Vs* (cons V^ Vs))
           (match args
             [(cons arg args*)
              (match arg
                [(EΡ ⟦E⟧ Ρ) {set (⟦E⟧ Ρ Φ^ (K+ (F:Ap Vs* args* ℓ) Ξ) Σ)}]
                [(? set? V^*) (↝ (K+ (F:Ap (cons V^* Vs*) args* ℓ) Ξ) Σ)])]
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
              (define Ρ* (bind-args! Ρ (-var xs #f) Vs H₀ Σ))
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
           (with-2-paths/collapse (λ () (split-results Σ R^₀))
             (λ ([Φ^ : Φ^]) {set (⟦E⟧₁ Ρ Φ^ Ξ Σ)})
             (λ ([Φ^ : Φ^]) {set (⟦E⟧₂ Ρ Φ^ Ξ Σ)}))))]
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
              [_ (let ([R^ (for/set : R^ ([W (in-set W^)]) (R W Φ^))])
                   (ret! R^ Ξ Σ))])}]
      [(F:Mon:C Ctx Ctc)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Val Φ^)
           (match Ctc
             [(EΡ ⟦C⟧ Ρ) {set (⟦C⟧ Ρ Φ^ (K+ (F:Mon:V Ctx Val) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon:V Ctx Val)
       (with-guarded-single-arity/collapse R^₀ (Ctx-loc Ctx)
         (λ (Ctc Φ^)
           (match Val
             [(EΡ ⟦V⟧ Ρ) {set (⟦V⟧ Ρ Φ^ (K+ (F:Mon:C Ctx Ctc) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon*:C Ctx rngs)
       (if rngs
           (with-guarded-arity/collapse R^₀ (length rngs) (Ctx-loc Ctx)
             (λ (W Φ^)
               (define-values (βs ℓs) (unzip-by αℓ-_0 αℓ-_1 rngs))
               (match* ((Σᵥ@* Σ βs) W ℓs)
                 [((cons C₁ Cs) (cons V₁ Vs) (cons ℓ₁ ℓs))
                  (define Ξ* (K+ (F:Mon* Ctx Cs Vs ℓs '()) Ξ))
                  (mon C₁ V₁ (Ctx-with-ℓ Ctx ℓ₁) Φ^ Ξ* Σ)]
                 [('() '() '())
                  {set (ret! (R '() Φ^) Ξ Σ)}])))
           {set (ret! R^₀ Ξ Σ)})]
      [(F:Mon* Ctx Cs Vs ℓs Res-rev)
       (define-values (W^ Φ^) (collapse-R^ R^₀))
       (match-define (list V^) (collapse-value-lists W^ 1))
       (define Res-rev* (cons V^ Res-rev))
       (match* (Cs Vs ℓs)
         [((cons C Cs) (cons V Vs) (cons ℓ ℓs))
          (define Ξ* (K+ (F:Mon* Ctx Cs Vs ℓs Res-rev*) Ξ))
          (mon C V (Ctx-with-ℓ Ctx ℓ) Φ^ Ξ* Σ)]
         [('() '() '())
          {set (ret! (R (reverse Res-rev*) Φ^) Ξ Σ)}])]
      [(F:Μ/C x)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (C-body Φ^)
           (define α (mk-α (-α:x/c x H₀)))
           (⊔ᵥ! Σ α C-body)
           {set (ret! (V->R (X/C α) Φ^) Ξ Σ)}))]
      [(F:==>:Dom inits↓ inits↑ ?rst rng Ρ ℓ ⇓?)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (V Φ^)
           (define inits↓* (cons V inits↓))
           {set (match inits↑
                  [(cons ⟦C⟧ ⟦C⟧s)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>:Dom inits↓* ⟦C⟧s ?rst rng Ρ ℓ ⇓?) Ξ) Σ)]
                  [_ (if ?rst
                         (?rst Ρ Φ^ (K+ (F:==>:Rst inits↓* rng Ρ ℓ ⇓?) Ξ) Σ)
                         (rng Ρ Φ^ (K+ (F:==>:Rng inits↓* #f ℓ ⇓?) Ξ) Σ))])}))]
      [(F:==>:Rst inits rng Ρ ℓ ⇓?)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (Vᵣ Φ^)
           {set (rng Ρ Φ^ (K+ (F:==>:Rng inits Vᵣ ℓ ⇓?) Ξ) Σ)}))]
      [(F:==>:Rng inits ?rst ℓ ⇓?)
       (define-values (D^ Φ^) (collapse-R^ R^₀))
       (define V (mk-==>! Σ H₀ inits ?rst D^ ℓ ⇓?))
       {set (ret! (V->R V Φ^) Ξ Σ)}]
      [(F:==>i Ρ doms↓ (cons x ℓ) doms↑ ⇓?)
       (with-guarded-single-arity/collapse R^₀ ℓ
         (λ (C^ Φ^)
           (define H (Ξ:co-ctx Ξ))
           (define α (mk-α (if (null? doms↑) (-α:rng ℓ H 0) (-α:dom ℓ H (length doms↓)))))
           (⊔ᵥ! Σ α C^)
           (define-values (doms↓₁ doms↑₁) (split-⟦dom⟧s Ρ doms↑))
           (define doms↓* (append doms↓₁ (cons (Dom x α ℓ) doms↓)))
           {set (match doms↑₁
                  [(cons (⟦dom⟧ x #f ⟦C⟧ ℓ) doms↑*)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>i Ρ doms↓* (cons x ℓ) doms↑* ⇓?) Ξ) Σ)]
                  ['()
                   (match-define (cons Rng Doms-rev) doms↓*)
                   (ret! (V->R (==>i (reverse Doms-rev) Rng ⇓?) Φ^) Ξ Σ)])}))]
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
      
      ;; Specific helpers
      [(F:Wrap G Ctx α)
       (with-guarded-single-arity/collapse R^₀ +ℓ₀ ; TODO
         (λ (V^ Φ^)
           (⊔ᵥ! Σ α V^)
           {set (ret! (V->R (X/G Ctx G α) Φ^) Ξ Σ)}))]
      [(F:Mon-Or/C ctx Cₗ Cᵣ V)
       (with-arity R^₀
         (match-lambda** ; TODO refine
          [(0 (R _ Φ^)) (mon Cᵣ V ctx Φ^ Ξ Σ)]
          [(1 R₁) {set (ret! R₁ Ξ Σ)}]))]
      [(F:If:Flat/C V^ Blm^)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (with-2-paths/collapse (λ () (split-results Σ R^₀))
             (λ ([Φ^ : Φ^]) {set (ret! (V->R V^ Φ^) Ξ Σ)})
             (λ _ Blm^))))]
      [(F:Fc-And/C α₁ αℓ₂)
       (with-arity R^₀
         (match-lambda**
          [(0 R₀) {set (ret! R₀ Ξ Σ)}]
          [(1 (R (list V) Φ^)) (match-define (αℓ α₂ ℓ₂) αℓ₂)  ; TODO refine
                               (fc (Σᵥ@ Σ α₂) V ℓ₂ Φ^ Ξ Σ)]))]
      [(F:Fc-Or/C α₁ αℓ₂ Vₓ)
       (with-arity R^₀
         (match-lambda** ; TODO refine
          [(0 (R _ Φ^)) (match-define (αℓ α₂ ℓ₂) αℓ₂)
                        (fc (Σᵥ@ Σ α₂) Vₓ ℓ₂ Φ^ Ξ Σ)]
          [(1 R₁) {set (ret! R₁ Ξ Σ)}]))]
      [(F:Fc-Not/C Vₓ)
       (with-arity R^₀
         (match-lambda**
          [(0 (R _ Φ^)) {set (ret! (R (list Vₓ) Φ^) Ξ Σ)}]
          [(1 (R _ Φ^)) {set (ret! (R '()       Φ^) Ξ Σ)}]))]
      [(F:Fc-Struct/C ℓ 𝒾 W-rev EΡs)
       (with-arity R^₀
         (match-lambda**
          [(0 R₀) {set (ret! R₀ Ξ Σ)}]
          [(1 (and R₁ (R (list V) Φ^)))
           {set (match EΡs
                  [(cons (cons ⟦E⟧ Ρ) EΡs)
                   (⟦E⟧ Ρ Φ^ (K+ (F:Fc-Struct/C ℓ 𝒾 (cons V W-rev) EΡs) Ξ) Σ)]
                  ['()
                   (define F:mk (F:Ap `(,@W-rev ,{set (-st-mk 𝒾)}) '() ℓ))
                   (ret! R₁ (K+ F:mk Ξ) Σ)])}]))]
      [(F:Fc:V ℓ ⟦V⟧ Ρ)
       (define-values (C^ Φ^) (collapse-R^-1 R^₀))
       {set (⟦V⟧ Ρ Φ^ (K+ (F:Fc:C ℓ C^) Ξ) Σ)}]
      [(F:Fc:C ℓ C^)
       (define-values (V^ Φ^) (collapse-R^-1 R^₀))
       (fc C^ V^ ℓ Φ^ Ξ Σ)]
      [(F:Hash-Set-Inner ℓ α)
       (with-arity R^₀
         (match-lambda**
          [(2 (R key-val Φ^))
           ((app₁ 'hash-set) (cons (Σᵥ@ Σ α) key-val) ℓ Φ^ Ξ Σ)]))]
      [(F:Set-Add-Inner ℓ α)
       (with-arity R^₀
         (match-lambda**
          [(2 (R (list Vₑ) Φ^))
           ((app₁ 'set-add) (list (Σᵥ@ Σ α) Vₑ) ℓ Φ^ Ξ Σ)]))]
      [(F:Maybe-Havoc-Prim-Args ℓ Symbol) ???]
      [(F:Make-Prim-Range ctx ?rng-wrap ranges cases) ???]
      [(F:Implement-Predicate P)
       (with-guarded-arity R^₀ 1 +ℓ₀
         (λ (R^₀)
           (define Rₐ
             (for*/union : R^ ([Rᵢ (in-set R^₀)])
               (match-define (R Wᵢ Φ^ᵢ) Rᵢ)
               (implement-predicate Σ Φ^ᵢ P Wᵢ)))
           {set (ret! Rₐ Ξ Σ)}))]
      [(F:Absurd) ∅]))

  (: ret! : (U R R^) Ξ:co Σ → Ξ:co)
  (define (ret! R Ξ Σ) (⊔ₐ! Σ Ξ R) Ξ)

  (: blm : ℓ -l (Listof (U V V^)) (U W W^) → (℘ Blm))
  (define (blm ℓ+ lo C Wₓ)
    (define (go [W : W]) (Blm (strip-ℓ ℓ+) lo C W))
    (cond [(not (transparent-module? (ℓ-src ℓ+))) ∅]
          [(set? Wₓ)
           (if (set-andmap (match-λ? (list _)) Wₓ)
               {set (go (list (foldl V⊔ ⊥V ((inst set-map W V^) Wₓ car))))}
               {map/set go Wₓ})]
          [else {set (go Wₓ)}]))

  (: with-arity (R^ (Index R → (℘ Ξ)) → (℘ Ξ)))
  (define (with-arity R^ handler)
    (define m : (Mutable-HashTable Index R) (make-hasheq))
    (for ([Rᵢ (in-set R^)])
      (define n (length (R-_0 Rᵢ)))
      (hash-set! m n (match (hash-ref m n #f)
                       [(? values R₀) (R⊔ R₀ Rᵢ)]
                       [#f Rᵢ])))
    (for/union : (℘ Ξ) ([(i Rᵢ) (in-hash m)]) (handler i Rᵢ)))

  (: with-guarded-arity/W : W Natural ℓ (W → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-arity/W W n ℓ exec)
    (if (= n (length W))
        (exec W)
        {set (Blm ℓ 'Λ (list 'arity (-b n)) W)}))

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

  (: with-guard : Σ Φ^ Ctx V^ P (R^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guard Σ Φ^ ctx V P exec)
    (with-2-paths (λ () (split-results Σ (R (list V) Φ^) P))
      exec
      (λ ([R^ : R^])
        (match-define (Ctx l+ _ lₒ ℓ) ctx)
        (blm (ℓ-with-src ℓ l+) lₒ (list P) (collapse-R^/W^ R^)))))

  (: mk-==>! : Σ H W (Option V^) W^ ℓ Boolean → V^)
  (define (mk-==>! Σ H₀ doms-rev ?rst rngs ℓ₀ ⇓?)
    (: mk-αℓs! : Symbol (ℓ H Index → -α) W → (Listof αℓ))
    (define (mk-αℓs! tag mk W)
      (for/list ([Vᵢ (in-list W)] [i (in-naturals)] #:when (index? i))
        (define αᵢ (mk-α (mk ℓ₀ H₀ i)))
        (⊔ᵥ! Σ αᵢ Vᵢ)
        (αℓ αᵢ (ℓ-with-id ℓ₀ (cons tag i)))))
    (define Dom (-var (mk-αℓs! 'dom -α:dom (reverse doms-rev))
                      (and ?rst (αℓ (mk-α (-α:rst ℓ₀ H₀)) (ℓ-with-id ℓ₀ 'rest)))))
    (for/set : V^ ([rng (in-set rngs)])
      (==> Dom
           (match rng
             [(list {singleton-set 'any}) #f]
             [_ (mk-αℓs! 'rng -α:rng rng)])
           ⇓?)))

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

  (: ↠ : ⟦E⟧ Ρ Φ^ Ξ:co Σ → (℘ Ξ))
  ;; Skip boring states. Use this for production. Not great for debugging.
  (define (↠ ⟦E⟧ Ρ Φ^ Ξ Σ)
    (define Ξ* (⟦E⟧ Ρ Φ^ Ξ Σ))
    (if (eq? Ξ* Ξ) (↝ Ξ* Σ) {set Ξ*}))

  (define db:iter? : (Parameterof Boolean) (make-parameter #f))
  (define db:max-steps : (Parameterof (Option Integer)) (make-parameter #f))
  )
