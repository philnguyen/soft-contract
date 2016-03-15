#lang typed/racket/base

(provide ev ev* co co* ⇓ₚ ⇓ₘ ⇓)

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "../proof-relation/main.rkt" "continuation.rkt")

(: ev* : -M -Ξ -σ (℘ -ℬ) → (Values -ΔM -ΔΞ -Δσ))
(define (ev* M Ξ σ ℬs)
  (for/fold ([δM : -ΔM ⊥M] [δΞ : -ΔΞ ⊥Ξ] [δσ : -Δσ ⊥σ])
            ([ℬ ℬs])
    (ev M Ξ σ ℬ)))

(: co* : -M -Ξ -σ (℘ -Co) → (Values -ΔM -ΔΞ -Δσ))
(define (co* M Ξ σ Cos)
  (for/fold ([δM : -ΔM ⊥M] [δΞ : -ΔΞ ⊥Ξ] [δσ : -Δσ ⊥σ])
            ([Co Cos])
    (co M Ξ σ Co)))

(: ev : -M -Ξ -σ -ℬ → (Values -ΔM -ΔΞ -Δσ))
;; Execute function body `ℬ`
(define (ev M Ξ σ ℬ)
  (apply/values (collect M Ξ ℬ) ((-ℬ-code ℬ) M σ ℬ)))

(: co : -M -Ξ -σ -Co → (Values -ΔM -ΔΞ -Δσ))
;; Resume computation `ℋ[A]`, propagating errors and plugging values into hole.
(define (co M Ξ σ Co)
  (match-define (-Co (-ℛ ℬ₀ ℋ₀) ℬ As) Co)
  (match-define (-ℋ Γ₀ f bnds ℰ) ℋ₀)

  ;; Propagate errors and plug values into hole
  (define-values (ΓWs ΓEs)
    (let ()
      (printf "TODO: use path-conditions from caller+callee to eliminate spurious returns~n")
      
      (define args (map (inst cdr Symbol -s) bnds))
      (define fargs (apply -?@ f args))
      
      (for/fold ([ΓWs : (℘ -ΓW) ∅] [ΓEs : (℘ -ΓE) ∅])
                ([A As])
        (define Γ₀*
          (match-let ([(-Γ φs as γs) Γ₀]
                      [γ (-γ ℬ f bnds)])
            (-Γ φs as (set-add γs γ))))
        (match A
          [(-ΓW Γ (-W Vs s))
           (values (set-add ΓWs (-ΓW Γ₀* (-W Vs (and s fargs)))) ΓEs)]
          [(-ΓE Γ blm)
           (values ΓWs (set-add ΓEs (-ΓE Γ₀* blm)))]))))
  
  (let ([col (collect M Ξ ℬ₀)])
    (⊔³ (apply/values col ((ℰ⟦_⟧ ℰ ΓWs) M σ ℬ₀))
        (apply/values col (values ⊥σ ∅ ΓEs ∅)))))
  

(: ⇓ₚ : (Listof -module) -e → -⟦e⟧)
;; Compile list of modules
(define (⇓ₚ ms e)
  (match ms
    ['() (⇓ e)]
    [(cons m ms*) ((↝.modules (map ⇓ₘ ms*) (⇓ e)) (⇓ₘ m))]))

(: ⇓ₘ : -module → -⟦e⟧)
;; Compile module
(define (⇓ₘ m)
  (match-define (-module p ds) m)
  
  (: ⇓pc : -provide-spec → -⟦e⟧)
  (define (⇓pc spec)
    (match-define (-p/c-item x c) spec)
    ((↝.dec (-id x p)) (⇓ c)))

  (: ⇓d : -module-level-form → -⟦e⟧)
  (define (⇓d d)
    (match d
      [(-define-values _ xs e) ((↝.def p xs) (⇓ e))]
      [(-provide _ specs) ((↝.begin (map ⇓pc specs)) ⟦void⟧)]
      [(? -e? e) (⇓ e)]
      [_
       (printf "⇓d: ignore ~a~n" (show-module-level-form d))
       ⟦void⟧]))

  ((↝.begin (map ⇓d ds)) ⟦void⟧))

(: ⇓ : -e → -⟦e⟧)
;; Compile expresion to computation
(define (⇓ e)
  (match e
    [(-λ xs e*)
     (define ⟦e*⟧ (⇓ e*))
     (λ (M σ ℬ)
       (match-define (-ℬ _ ρ Γ _) ℬ)
       (values ⊥σ {set (-ΓW Γ (-W (list (-Clo xs ⟦e*⟧ ρ Γ)) e))} ∅ ∅))]
    [(-case-λ body) (error '⇓ "TODO: case-λ")]
    [(? -prim? p)
     (λ (M σ ℬ)
       (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) (-W (list p) p))} ∅ ∅))]
    [(-• i)
     (λ (M σ ℬ)
       (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) (-W -●/Vs e))} ∅ ∅))]
    [(-x x)
     (λ (M σ ℬ)
       (match-define (-ℬ _ ρ Γ 𝒞) ℬ)
       (define s (canonicalize Γ x))
       (define-values (ΓWs ΓEs)
         (for*/fold ([ΓWs : (℘ -ΓW) ∅]
                     [ΓEs : (℘ -ΓE) ∅])
                    ([V (σ@ σ (ρ@ ρ x))]
                     [W (in-value (-W (list V) s))]
                     #:unless (spurious? M σ Γ W))
           (case V
             [(undefined) ; spurious `undefined` should have been eliminated by `spurious?`
              (values
               ΓWs
               (set-add
                ΓEs
                (-ΓE Γ (-blm 'TODO 'Λ (list 'defined?) (list 'undefined)))))]
             [else (values (set-add ΓWs (-ΓW Γ W)) ΓEs)])))
       (values ⊥σ ΓWs ΓEs ∅))]
    [(and ref (-ref (and id (-id name l-from)) l-ctx pos))
     (cond
       [(equal? l-from l-ctx)
        (λ (M σ ℬ)
          (define Γ (-ℬ-cnd ℬ))
          (define ΓWs
            (for/set: : (℘ -ΓW) ([V (σ@ σ (-α.def id))])
              (define s (if (-o? V) V ref))
              (-ΓW Γ (-W (list V) s))))
          (values ⊥σ ΓWs ∅ ∅))]
       [else
        (λ (M σ ℬ)
          (printf "FIXME: ignore `~a`'s contract for now.~n" (-id-name id))
          (define Γ (-ℬ-cnd ℬ))
          (define ΓWs
            (for/set: : (℘ -ΓW) ([V (σ@ σ (-α.def id))])
              (define s (if (-o? V) V ref))
              (-ΓW Γ (-W (list V) s))))
          (values ⊥σ ΓWs ∅ ∅))])]
    [(-@ f xs l)
     ((↝.@ '() (map ⇓ xs) l) (⇓ f))]
    [(-if e₀ e₁ e₂)
     ((↝.if (⇓ e₁) (⇓ e₂)) (⇓ e₀))]
    [(-wcm k v b)
     (error '⇓ "TODO: wcm")]
    [(-begin es)
     (match es
       [(cons e* es*) ((↝.begin (map ⇓ es*)) (⇓ e*))]
       ['() ⟦void⟧])]
    [(-begin0 e₀ es)
     ((↝.begin0.v (map ⇓ es)) (⇓ e₀))]
    [(-quote q)
     (cond
       [(Base? q)
        (define b (-b q))
        (λ (M σ ℬ)
          (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) (-W (list b) b))} ∅ ∅))]
       [else (error '⇓ "TODO: (quote ~a)" q)])]
    [(-let-values xs-es e l)
     (define ⟦e⟧ (⇓ e))
     (define xs-⟦e⟧s
       (for/list : (Listof (Pairof (Listof Symbol) -⟦e⟧)) ([xs-e xs-es])
         (match-define (cons xs eₓ) xs-e)
         (cons xs (⇓ eₓ))))
     (match xs-⟦e⟧s 
       ['() ⟦e⟧]
       [(cons (cons xs₀ ⟦e⟧₀) xs-⟦eₓ⟧s*)
        ((↝.let-values '() xs₀ xs-⟦eₓ⟧s* ⟦e⟧ l) ⟦e⟧₀)])]
    [(-letrec-values xs-es e l)
     (define ⟦e⟧ (⇓ e))
     (define xs-⟦e⟧s
       (for/list : (Listof (Pairof (Listof Symbol) -⟦e⟧)) ([xs-e xs-es])
         (match-define (cons xs eₓ) xs-e)
         (cons xs (⇓ eₓ))))
     (match xs-⟦e⟧s
       ['() ⟦e⟧]
       [(cons (cons xs₀ ⟦e⟧₀) xs-⟦e⟧s*)
        (λ (M σ ℬ)
          (define 𝒞 (-ℬ-hist ℬ))
          (define-values (δσ δρ)
            (for*/fold ([δσ : -Δσ ⊥σ] [δρ : -Δρ ⊥ρ])
                       ([xs-⟦e⟧ xs-⟦e⟧s] [x (car xs-⟦e⟧)])
              (define α (-α.x x 𝒞))
              (values (⊔ δσ α 'undefined)
                      (hash-set δρ x α))))
          (define σ* (⊔/m σ δσ))
          (((↝.letrec-values δρ xs₀ xs-⟦e⟧s* ⟦e⟧ l) ⟦e⟧₀) M σ* ℬ))])]
    [(-set! x e*) ((↝.set! x) (⇓ e*))]
    [(-@-havoc (-x x)) (↝.havoc x)]
    [(-amb es)
     (define ⟦e⟧s (set-map es ⇓))
     (λ (M σ ℬ)
       (for*/ans ([⟦e⟧ ⟦e⟧s]) (⟦e⟧ M σ ℬ)))]
    [(-μ/c x c) ((↝.μ/c x) (⇓ c))]
    [(-->i cs (and mk-d (-λ xs d)) l)
     (define ⟦d⟧ (⇓ d))
     (match (map ⇓ cs)
       ['()
        (define c (-?->i '() mk-d))
        (λ (M σ ℬ)
          (match-define (-ℬ _ ρ Γ _) ℬ)
          (define Mk-D (-W¹ (-Clo xs ⟦d⟧ ρ Γ) mk-d))
          (mk-=>i Γ '() Mk-D l))]
       [(cons ⟦c⟧ ⟦c⟧s*)
        (λ (M σ ℬ)
          (match-define (-ℬ _ ρ Γ _) ℬ)
          (define Mk-D (-W¹ (-Clo xs ⟦d⟧ ρ Γ) mk-d))
          (((↝.-->i '() ⟦c⟧s* Mk-D l) ⟦c⟧) M σ ℬ))])]
    [(-x/c x)
     (λ (M σ ℬ)
       (define Γ (-ℬ-cnd ℬ))
       (define ΓWs
         (for/set: : (℘ -ΓW) ([V (σ@ σ (-α.x/c x))])
           (-ΓW Γ (-W (list V) e))))
       (values ⊥σ ΓWs ∅ ∅))]
    [(-struct/c si cs l)
     (match cs
       ['()
        (λ (M σ ℬ)
          (define V (-St/C #t si '()))
          (define W (-W (list V) e))
          (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) W)} ∅ ∅))]
       [(cons c cs*)
        ((↝.struct/c si '() (map ⇓ cs*) l) (⇓ c))])]))

(: ℰ⟦_⟧ : -ℰ (℘ -ΓW) → -⟦e⟧)
;; Plug answers `ΓWs` into hole `ℰ` and resume computation
;; Stacks `ℰ` are finite, but I can't "compile" them ahead of time because they depend on
;; "run-time" `V`. Using functions instead of flat values to represent `ℰ` may generate
;; infinitely many equivalent but distinct (Racket-level) functions.
;; Memoization might help, but I doubt it speeds up anything.
;; So I'll keep things simple for now.
(define (ℰ⟦_⟧ ℰ ΓWs)
  (let go : -⟦e⟧ ([ℰ : -ℰ ℰ])
    (match ℰ
      ;; Hacky forms
      [(-ℰₚ.modules ℰ* ⟦m⟧s ⟦e⟧) ((↝.modules ⟦m⟧s ⟦e⟧) (go ℰ*))]
      [(-ℰ.def m xs ℰ*) ((↝.def m xs) (go ℰ*))]
      [(-ℰ.dec id ℰ*) ((↝.dec id) (go ℰ*))]
      ;; Regular forms
      ['□ (λ _ (values ⊥σ ΓWs ∅ ∅))]
      [(-ℰ.if ℰ* ⟦e₁⟧ ⟦e₂⟧) ((↝.if ⟦e₁⟧ ⟦e₂⟧) (go ℰ*))]
      [(-ℰ.@ WVs ℰ* ⟦e⟧s loc) ((↝.@ WVs ⟦e⟧s loc) (go ℰ*))]
      [(-ℰ.begin ℰ* ⟦e⟧s) ((↝.begin ⟦e⟧s) (go ℰ*))]
      [(-ℰ.begin0.v ℰ* ⟦e⟧s) ((↝.begin0.v ⟦e⟧s) (go ℰ*))]
      [(-ℰ.begin0.e W ℰ* ⟦e⟧s) ((↝.begin0.e W ⟦e⟧s) (go ℰ*))]
      [(-ℰ.let-values xs-Ws (cons xs ℰ*) xs-⟦e⟧s ⟦e⟧ l)
       ((↝.let-values xs-Ws xs xs-⟦e⟧s ⟦e⟧ l) (go ℰ*))]
      [(-ℰ.letrec-values δρ (cons xs ℰ*) xs-⟦e⟧s ⟦e⟧ l)
       ((↝.letrec-values δρ xs xs-⟦e⟧s ⟦e⟧ l) (go ℰ*))]
      [(-ℰ.set! x ℰ*) ((↝.set! x) (go ℰ*))]
      [(-ℰ.μ/c x ℰ*) ((↝.μ/c x) (go ℰ*))]
      [(-ℰ.-->i Cs ℰ* ⟦c⟧s ⟦mk-d⟧ l)
       ((↝.-->i Cs ⟦c⟧s ⟦mk-d⟧ l) (go ℰ*))]
      [(-ℰ.struct/c si Cs ℰ* ⟦c⟧s l)
       ((↝.struct/c si Cs ⟦c⟧s l) (go ℰ*))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊔³ x y)
  (let-values ([(m₁ m₂ m₃) x]
               [(n₁ n₂ n₃) y])
    (values (⊔/m m₁ n₁) (⊔/m m₂ n₂) (⊔/m m₃ n₃))))

(: collect : -M -Ξ -ℬ → -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ) → (Values -ΔM -ΔΞ -Δσ))
;; Collect evaluation results into store deltas
(define ((collect M Ξ ℬ) δσ ΓWs ΓEs ℐs)
  
  (define δM : -ΔM
    (let* ([As (M@ M ℬ)]
           [δ-As (-- (∪ ΓWs ΓEs) As)])
      (if (set-empty? δ-As) ⊥M (hash ℬ δ-As))))
  
  (define δΞ
    (for*/fold ([δΞ : -ΔΞ ⊥Ξ])
               ([ℐ ℐs]
                [ℋ  (in-value (-ℐ-hole ℐ))]
                [ℬ* (in-value (-ℐ-target ℐ))]
                [ℛ  (in-value (-ℛ ℬ ℋ))]
                #:unless (m∋ Ξ ℬ* ℛ))
      (⊔ δΞ ℬ* ℛ)))
  
  (values δM δΞ δσ))

(: ⇓const : Base → -⟦e⟧)
(define (⇓const b)
  (define W (let ([B (-b b)]) (-W (list B) B)))
  (λ (M σ ℬ)
    (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) W)} ∅ ∅)))

(define ⟦void⟧ (⇓const (void)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;(define (ev₁ [e : -e])
  (define-values (δM δΞ δσ) (ev ⊥M ⊥Ξ ⊥σ (-ℬ (⇓ e) ⊥ρ)))
  (values (show-M δM) (show-Ξ δΞ) (show-σ δσ)))
