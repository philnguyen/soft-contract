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
          alloc^ app^ mon^ fc^ compile^ havoc^ approx^)
  (export step^)

  (: inj : (U -prog ⟦E⟧) → (Values Ξ Σ))
  (define (inj x)
    (define ⟦E⟧ (->⟦E⟧ x))
    (define αₖ₀ (αₖ:clo ⟦E⟧ ⊥Ρ))
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
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (T^ Φ^)
           (define Vs* (cons T^ Vs))
           (match args
             [(cons arg args*)
              (match arg
                [(EΡ ⟦E⟧ Ρ) {set (⟦E⟧ Ρ Φ^ (K+ (F:Ap Vs* args* ℓ) Ξ) Σ)}]
                [(? set? T^*) (↝ (K+ (F:Ap (cons T^* Vs*) args* ℓ) Ξ) Σ)])]
             [_ (match-define (cons fun args) (reverse Vs*))
                (app fun args ℓ Φ^ Ξ Σ)])))]
      [(F:Set! α)
       (with-guarded-single-arity/collapse Σ R^₀ +ℓ₀ ; TODO
         (λ (T^ Φ^)
           (⊔T! Σ Φ^ α T^)
           {set (ret! (T->R -void Φ^) Ξ Σ)}))]
      [(F:Let ℓ xs binds bounds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse Σ R^₀ (length xs) ℓ
         (λ (W Φ^)
           (define bounds*
             (for/fold ([acc : (Assoc Symbol T^) bounds])
                       ([x (in-list xs)] [V (in-list W)])
               (cons (cons x V) acc)))
           (match binds
             [(cons (cons xs* ⟦E⟧) binds*)
              {set (⟦E⟧ Ρ Φ^ (K+ (F:Let ℓ xs* binds* bounds* ⟦body⟧ Ρ) Ξ) Σ)}]
             ['()
              (define-values (xs Vs) (unzip bounds*))
              (define-values (Φ^* Ρ*) (bind-args! Φ^ Ρ (-var xs #f) Vs H₀ Σ))
              {set (⟦body⟧ Ρ* Φ^* Ξ Σ)}])))]
      [(F:Letrec ℓ xs binds ⟦body⟧ Ρ)
       (with-guarded-arity/collapse Σ R^₀ (length xs) ℓ
         (λ (W Φ^)
           (⊔T*! Σ Φ^ (Ρ@* Ρ xs) W)
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
       (with-guarded-single-arity/collapse Σ R^₀ (Ctx-loc Ctx)
         (λ (Val Φ^)
           (match Ctc
             [(EΡ ⟦C⟧ Ρ) {set (⟦C⟧ Ρ Φ^ (K+ (F:Mon:V Ctx Val) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon:V Ctx Val)
       (with-guarded-single-arity/collapse Σ R^₀ (Ctx-loc Ctx)
         (λ (Ctc Φ^)
           (match Val
             [(EΡ ⟦V⟧ Ρ) {set (⟦V⟧ Ρ Φ^ (K+ (F:Mon:C Ctx Ctc) Ξ) Σ)}]
             [(? set?) (mon Ctc Val Ctx Φ^ Ξ Σ)])))]
      [(F:Mon*:C Ctx rngs)
       (if rngs
           (with-guarded-arity/collapse Σ R^₀ (length rngs) (Ctx-loc Ctx)
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
       (match-define (R (list T^) Φ^) (collapse-value-lists Σ R^₀ 1))
       (define Res-rev* (cons T^ Res-rev))
       (match* (Cs Vs ℓs)
         [((cons C Cs) (cons V Vs) (cons ℓ ℓs))
          (define Ξ* (K+ (F:Mon* Ctx Cs Vs ℓs Res-rev*) Ξ))
          (mon C V (Ctx-with-ℓ Ctx ℓ) Φ^ Ξ* Σ)]
         [('() '() '())
          {set (ret! (R (reverse Res-rev*) Φ^) Ξ Σ)}])]
      [(F:Μ/C x)
       (with-guarded-single-arity/collapse Σ R^₀ +ℓ₀ ; TODO
         (λ (C-body Φ^)
           (define α (mk-α (-α:x/c x H₀)))
           (⊔T! Σ Φ^ α C-body)
           {set (ret! (T->R (X/C α) Φ^) Ξ Σ)}))]
      [(F:==>:Dom inits↓ inits↑ ?rst rng Ρ ℓ)
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (V Φ^)
           (define inits↓* (cons V inits↓))
           {set (match inits↑
                  [(cons ⟦C⟧ ⟦C⟧s)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>:Dom inits↓* ⟦C⟧s ?rst rng Ρ ℓ) Ξ) Σ)]
                  [_ (if ?rst
                         (?rst Ρ Φ^ (K+ (F:==>:Rst inits↓* rng Ρ ℓ) Ξ) Σ)
                         (rng Ρ Φ^ (K+ (F:==>:Rng inits↓* #f ℓ) Ξ) Σ))])}))]
      [(F:==>:Rst inits rng Ρ ℓ)
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (Vᵣ Φ^)
           {set (rng Ρ Φ^ (K+ (F:==>:Rng inits Vᵣ ℓ) Ξ) Σ)}))]
      [(F:==>:Rng inits ?rst ℓ)
       (define-values (D^ Φ^) (collapse-R^ R^₀))
       (define V (mk-==>! Σ Φ^ H₀ inits ?rst D^ ℓ))
       {set (ret! (T->R V Φ^) Ξ Σ)}]
      [(F:==>i Ρ doms↓ (cons x ℓ) doms↑)
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (C^ Φ^)
           (define H (Ξ:co-ctx Ξ))
           (define α (mk-α (if (null? doms↑) (-α:rng ℓ H 0) (-α:dom ℓ H (length doms↓)))))
           (⊔T! Σ Φ^ α C^)
           (define-values (doms↓₁ doms↑₁) (split-⟦dom⟧s Ρ doms↑))
           (define doms↓* (append doms↓₁ (cons (Dom x α ℓ) doms↓)))
           {set (match doms↑₁
                  [(cons (⟦dom⟧ x #f ⟦C⟧ ℓ) doms↑*)
                   (⟦C⟧ Ρ Φ^ (K+ (F:==>i Ρ doms↓* (cons x ℓ) doms↑*) Ξ) Σ)]
                  ['()
                   (match-define (cons Rng Doms-rev) doms↓*)
                   (ret! (T->R (==>i (reverse Doms-rev) Rng) Φ^) Ξ Σ)])}))]
      [(F:St/C ℓ 𝒾 Cs ⟦C⟧s Ρ)
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (C^ Φ^)
           (define Cs* (cons C^ Cs))
           {set (match ⟦C⟧s
                  [(cons ⟦C⟧ ⟦C⟧s*)
                   (⟦C⟧ Ρ Φ^ (K+ (F:St/C ℓ 𝒾 Cs* ⟦C⟧s* Ρ) Ξ) Σ)]
                  [_
                   (define flds (mk-αℓ*! Σ Φ^ (-𝒾-name 𝒾) (curry -α:struct/c 𝒾) H₀ ℓ (reverse Cs*)))
                   (define flat? (andmap C^-flat? Cs*))
                   (ret! (T->R (St/C flat? 𝒾 flds) Φ^) Ξ Σ)])}))]
      [(F:Def l lhs)
       (with-guarded-arity/collapse Σ R^₀ (length lhs) +ℓ₀ ; TODO
         (λ (W Φ^)
           (⊔T*! Σ Φ^ lhs W)
           (define Φ^*
             (for/fold ([acc : (℘ Φ) Φ^])
                       ([α (in-list lhs)] [T (in-list W)] #:unless (mutable? α))
               ($+ acc α (if (S? T) T (S:α α)))))
           (↝ (ret! (T->R -void Φ^*) Ξ Σ) Σ)))]
      [(F:Dec ℓ 𝒾)
       (with-guarded-single-arity/collapse Σ R^₀ ℓ
         (λ (C^ Φ^)
           (define l (-𝒾-src 𝒾))
           (define α  (mk-α (-α:top 𝒾)))
           (define α* (mk-α (-α:wrp 𝒾)))
           (define T^ (Σᵥ@ Σ α))
           (define Φ^* ($+ Φ^ α* (S:α α*)))
           (mon C^ T^ (Ctx l 'dummy- l ℓ) Φ^* (K+ (F:Def l (list α*)) Ξ) Σ)))]
      
      ;; Specific helpers
      [(F:Wrap G Ctx α)
       (with-guarded-single-arity/collapse Σ R^₀ +ℓ₀ ; TODO
         (λ (T^ Φ^)
           (⊔T! Σ Φ^ α T^)
           {set (ret! (T->R (X/G Ctx G α) Φ^) Ξ Σ)}))]
      [(F:Mon-Or/C ctx Cₗ Cᵣ V)
       (with-arity Σ R^₀
         (match-lambda** ; TODO refine
          [(0 (R _ Φ^)) (mon Cᵣ V ctx Φ^ Ξ Σ)]
          [(1 R₁) {set (ret! R₁ Ξ Σ)}]))]
      [(F:If:Flat/C T^ Blm^)
       (with-guarded-arity R^₀ 1 +ℓ₀ ; TODO
         (λ (R^₀)
           (with-2-paths/collapse (λ () (split-results Σ R^₀))
             (λ ([Φ^ : Φ^]) {set (ret! (T->R T^ Φ^) Ξ Σ)})
             (λ _ Blm^))))]
      [(F:Fc-And/C α₁ αℓ₂)
       (with-arity Σ R^₀
         (match-lambda**
          [(0 R₀) {set (ret! R₀ Ξ Σ)}]
          [(1 (R (list V) Φ^)) (match-define (αℓ α₂ ℓ₂) αℓ₂)  ; TODO refine
                               (fc (Σᵥ@ Σ α₂) V ℓ₂ Φ^ Ξ Σ)]))]
      [(F:Fc-Or/C α₁ αℓ₂ Vₓ)
       (with-arity Σ R^₀
         (match-lambda** ; TODO refine
          [(0 (R _ Φ^)) (match-define (αℓ α₂ ℓ₂) αℓ₂)
                        (fc (Σᵥ@ Σ α₂) Vₓ ℓ₂ Φ^ Ξ Σ)]
          [(1 R₁) {set (ret! R₁ Ξ Σ)}]))]
      [(F:Fc-Not/C Vₓ)
       (with-arity Σ R^₀
         (match-lambda**
          [(0 (R _ Φ^)) {set (ret! (R (list Vₓ) Φ^) Ξ Σ)}]
          [(1 (R _ Φ^)) {set (ret! (R '()       Φ^) Ξ Σ)}]))]
      [(F:Fc-Struct/C ℓ 𝒾 W-rev EΡs)
       (with-arity Σ R^₀
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
       (define-values (C^ Φ^) (collapse-R^-1 Σ R^₀))
       {set (⟦V⟧ Ρ Φ^ (K+ (F:Fc:C ℓ C^) Ξ) Σ)}]
      [(F:Fc:C ℓ C^)
       (define-values (T^ Φ^) (collapse-R^-1 Σ R^₀))
       (fc C^ T^ ℓ Φ^ Ξ Σ)]
      [(F:Hash-Set-Inner ℓ α)
       (with-arity Σ R^₀
         (match-lambda**
          [(2 (R key-val Φ^))
           ((app₁ 'hash-set) (cons (Σᵥ@ Σ α) key-val) ℓ Φ^ Ξ Σ)]))]
      [(F:Set-Add-Inner ℓ α)
       (with-arity Σ R^₀
         (match-lambda**
          [(2 (R (list Vₑ) Φ^))
           ((app₁ 'set-add) (list (Σᵥ@ Σ α) Vₑ) ℓ Φ^ Ξ Σ)]))]
      [(F:Havoc-Prim-Args ℓ Symbol)
       (define Tₕᵥ
         (for*/set : V^ ([R₀ (in-set R^₀)]
                         [Φ^₀ (in-value (R-_1 R₀))]
                         [T (in-list (R-_0 R₀))]
                         [V (in-set (T->V Σ Φ^₀ T))] #:when (behavioral? Σ V))
           V))
       (cond [(set-empty? Tₕᵥ) {set (ret! R^₀ Ξ Σ)}]
             [else (define ℓ* (ℓ-with-id ℓ 'prim-havoc) )
                   (define Φ^* (collapse-R^/Φ^ R^₀))
                   (app-opq (list Tₕᵥ) ℓ* Φ^* Ξ Σ)])]
      [(F:Make-Prim-Range ctx ?rng-wrap ranges cases)
       (define R^₁ (refine-ranges Σ cases R^₀ ranges))
       (define Ξ* (if ?rng-wrap (K+ (F:Mon*:C ctx ?rng-wrap) Ξ) Ξ))
       {set (ret! R^₁ Ξ* Σ)}]
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
          [(set? Wₓ) {map/set go Wₓ}]
          [else {set (go Wₓ)}]))

  (: with-arity ((U Σ Σᵥ) R^ (Index R → (℘ Ξ)) → (℘ Ξ)))
  (define (with-arity Σ R^ handler)
    (define m : (Mutable-HashTable Index R) (make-hasheq))
    (for ([Rᵢ (in-set R^)])
      (define n (length (R-_0 Rᵢ)))
      (hash-set! m n (match (hash-ref m n #f)
                       [(? values R₀) (R⊕ Σ R₀ Rᵢ)]
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
  
  (: with-guarded-arity/collapse : Σ R^ Natural ℓ (W Φ^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-arity/collapse Σ R^ n ℓ exec)
    (with-guarded-arity R^ n ℓ
      (λ (R^-goods)
        (match-define (R W Φ^) (collapse-value-lists Σ R^-goods n))
        (exec W Φ^))))

  (: with-guarded-single-arity/collapse : Σ R^ ℓ (T^ Φ^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-guarded-single-arity/collapse Σ R^ ℓ exec)
    (with-guarded-arity/collapse Σ R^ 1 ℓ (λ (W Φ^) (exec (car W) Φ^))))

  (: with-check : Σ Φ^ Ctx T^ P (R^ → (℘ Ξ)) → (℘ Ξ))
  (define (with-check Σ Φ^ ctx V P exec)
    (with-2-paths (λ () (split-results Σ (R (list V) Φ^) P))
      exec
      (λ ([R^ : R^])
        (match-define (Ctx l+ _ lₒ ℓ) ctx)
        (blm (ℓ-with-src ℓ l+) lₒ (list P) (collapse-R^/W^ R^)))))

  (: mk-==>! : Σ Φ^ H W (Option T^) W^ ℓ → (℘ ==>))
  (define (mk-==>! Σ Φ^ H₀ doms-rev ?rst rngs ℓ₀)
    (: mk-αℓs! : Symbol (ℓ H Index → -α) W → (Listof αℓ))
    (define (mk-αℓs! tag mk W)
      (for/list ([Tᵢ (in-list W)] [i (in-naturals)] #:when (index? i))
        (define αᵢ (mk-α (mk ℓ₀ H₀ i)))
        (⊔T! Σ Φ^ αᵢ Tᵢ)
        (αℓ αᵢ (ℓ-with-id ℓ₀ (cons tag i)))))
    (define Dom (-var (mk-αℓs! 'dom -α:dom (reverse doms-rev))
                      (and ?rst (αℓ (mk-α (-α:rst ℓ₀ H₀)) (ℓ-with-id ℓ₀ 'rest)))))
    (for/set : (℘ ==>) ([rng (in-set rngs)])
      (==> Dom (match rng
                 [(list {singleton-set 'any}) #f]
                 [_ (mk-αℓs! 'rng -α:rng rng)]))))

  (: K+/And : -l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)
  (define (K+/And l ⟦E⟧s Ρ Ξ)
    (match ⟦E⟧s
      [(cons ⟦E⟧ ⟦E⟧s) (K+ (F:If l ⟦E⟧ (mk-T -ff) Ρ) (K+/And l ⟦E⟧s Ρ Ξ))]
      [_ Ξ]))

  (: K+/Or : -l (Listof ⟦E⟧) Ρ Ξ:co → Ξ:co)
  (define (K+/Or l ⟦E⟧s Ρ Ξ)
    (match ⟦E⟧s
      [(cons ⟦E⟧ ⟦E⟧s) (K+ (F:If l (mk-T -tt) ⟦E⟧ Ρ) (K+/Or l ⟦E⟧s Ρ Ξ))]
      [_ Ξ]))

  (: mk-αℓ*! : Σ Φ^ Symbol (ℓ H Index → -α) H ℓ W → (Listof αℓ))
  (define (mk-αℓ*! Σ Φ^ tag mk H ℓ Ts)
    (for/list ([T (in-list Ts)] [i (in-naturals)] #:when (index? i))
      (define α (mk-α (mk ℓ H i)))
      (⊔T! Σ Φ^ α T)
      (αℓ α (ℓ-with-id ℓ (cons tag i)))))

  (: refine-ranges : Σ (Listof (List (Listof V) (Option V) (Listof V))) R^ W → R^)
  (define (refine-ranges Σ cases arg-lists rng) 

    (: go-arg : R → R)
    (define (go-arg R-args)
      (match-define (R args Φ^₀) R-args)

      (: obvious? : V T^ → Boolean)
      (define (obvious? p xs)
        (define (⊢ [o : V] [T^ : T^]) : ?Dec
          (match o
            [(Not/C (αℓ (app inspect-α (-α:imm C)) _))
             (case (⊢ C T^)
               [(✓) '✗]
               [(✗) '✓]
               [else #f])]
            [(? P? P)
             (let-values ([(R✓ R✗ R?)
                           (partition-results Σ (R (list T^) Φ^₀) o #:fast? #t)])
               (and (set-empty? R?)
                    (or (and (set-empty? R✗) '✓)
                        (and (set-empty? R✓) '✗))))]
            [_ #f]))
        (eq? (⊢ p xs) '✓))

      (for/fold ([R* : R (R rng Φ^₀)]) ([kase (in-list cases)])
        (match-define (list dom-inits ?dom-rst refinements) kase)

        (: check-inits : (Listof V) (Listof T^) → R)
        (define check-inits
          (match-lambda**
           [((cons dom doms*) (cons arg args*))
            (if (obvious? dom arg) (check-inits doms* args*) R*)]
           [('() args) (check-rest args)]
           [((cons _ _) '()) R*]))

        (: check-rest : (Listof T^) → R)
        (define (check-rest args)
          (cond
            [?dom-rst
             (let go ([args : (Listof T^) args])
               (match args
                 ['() (refine-rng)]
                 [(cons arg args*) (if (obvious? ?dom-rst arg) (go args*) R*)]))]
            [else (if (null? args) (refine-rng) R*)]))

        (define (refine-rng)
          (define-values (rng-rev Φ^*)
            (for/fold ([rng-rev : (Listof T^) '()] [Φ^ : Φ^ (R-_1 R*)])
                      ([rngᵢ (in-list (R-_0 R*))]
                       [refᵢ (in-list refinements)])
              (values (cons (V^+ rngᵢ refᵢ) rng-rev)
                      (if (and (P? refᵢ) (S? rngᵢ))
                          (Ψ+ Φ^ refᵢ (list rngᵢ))
                          Φ^))))
          (R (reverse rng-rev) Φ^*))

        (check-inits dom-inits args)))

    (map/set go-arg arg-lists))

  (: ↠ : ⟦E⟧ Ρ Φ^ Ξ:co Σ → (℘ Ξ))
  ;; Skip boring states. Use this for production. Not great for debugging.
  (define (↠ ⟦E⟧ Ρ Φ^ Ξ Σ)
    (define Ξ* (⟦E⟧ Ρ Φ^ Ξ Σ))
    (if (eq? Ξ* Ξ) (↝ Ξ* Σ) {set Ξ*}))

  (define db:iter? : (Parameterof Boolean) (make-parameter #f))
  (define db:max-steps : (Parameterof (Option Integer)) (make-parameter #f))
  )
