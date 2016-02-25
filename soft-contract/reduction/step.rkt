#lang typed/racket/base

(provide ev ev* co co* ⇓ₚ ⇓ₘ ⇓)

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "../proof-relation/main.rkt" "continuation.rkt")

(: ev* : -M -Ξ -σ (℘ -ℬ) → (Values -ΔM -ΔΞ -Δσ))
(define (ev* M Ξ σ ℬs)
  (for/fold ([δM : -ΔM ⊥M] [δΞ : -ΔΞ ⊥Ξ] [δσ : -Δσ ⊥σ]) ([ℬ ℬs])
    (ev M Ξ σ ℬ)))

(: co* : -M -Ξ -σ (℘ -Co) → (Values -ΔM -ΔΞ -Δσ))
(define (co* M Ξ σ Cos)
  (for/fold ([δM : -ΔM ⊥M] [δΞ : -ΔΞ ⊥Ξ] [δσ : -Δσ ⊥σ]) ([Co Cos])
    (co M Ξ σ Co)))

(: ev : -M -Ξ -σ -ℬ → (Values -ΔM -ΔΞ -Δσ))
;; Execute function body `ℬ`
(define (ev M Ξ σ ℬ)
  (match-define (-ℬ ⟦e⟧ ρ) ℬ)
  ;; start of function body, so trivial path condition `⊤Γ` and aliasing `⊤𝒳`
  (apply/values (collect M Ξ ℬ) (⟦e⟧ M σ ρ ⊤Γ ⊤𝒳)))

(: co : -M -Ξ -σ -Co → (Values -ΔM -ΔΞ -Δσ))
;; Resume computation `Co`
(define (co M Ξ σ Co)
  (match-define (-Co (-ℛ ℬ ℋ) As) Co)
  (match-define (-ℬ _ ρ) ℬ)
  (match-define (-ℋ Γ 𝒳 f bnds ℰ) ℋ)

  (define As* : (Setof -A)
    (let ()
      (printf "TODO: use `Γ`, `f`, and `𝒳*` to filter out spurious returns~n")
      
      (define 𝒳*
        (for/hash : -𝒳 ([bnd bnds] #:when (cdr bnd))
          (values (car bnd) (cdr bnd))))
      (define args (map (inst cdr Symbol -s) bnds))
      (define fargs (apply -?@ f args))
      
      (map/set
       (match-lambda
         [(-A _ res)
          (-A
           Γ
           (match res
             [(-W Vs s)
              (define γ (and s fargs (-γ (assert f) (cast args (Listof -e)) 𝒳*)))
              (-W Vs γ)]
             [blm blm]))])
       As)))
  
  (apply/values (collect M Ξ ℬ) ((ℰ⟦_⟧ ℰ As*) M σ ρ Γ 𝒳)))

(: ⇓ₚ : (Listof -module) -e → -⟦e⟧)
;; Compile list of modules
(define (⇓ₚ ms e)
  (match ms
    [(cons m ms*) ((↝.modules (map ⇓ₘ ms*) (⇓ e)) (⇓ₘ m))]
    [_ (⇓ e)]))

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
;; Compile expresion to mapping from store to (potentially suspended) results
(define (⇓ e)
  (match e
    [(-λ xs e*)
     (define ⟦e*⟧ (⇓ e*))
     (λ (G σ ρ Γ 𝒳)
       (values ⊥σ {set (-A Γ (-W (list (-Clo xs ⟦e*⟧ ρ)) e))} ∅))]
    [(-case-λ body) (error '⇓ "TODO: case-λ")]
    [(? -prim? p)
     (λ (G σ ρ Γ 𝒳)
       (values ⊥σ {set (-A Γ (-W (list p) p))} ∅))]
    [(-• i)
     (λ (G σ ρ Γ 𝒳)
       (values ⊥σ {set (-A Γ (-W -●/Vs e))} ∅))]
    [(-x x)
     (λ (G σ ρ Γ 𝒳)
       (define s (canonicalize 𝒳 x))
       (define As
         (for*/fold ([As : (℘ -A) ∅])
                    ([V (σ@ σ (ρ@ ρ x))]
                     [W (in-value (-W (list V) s))]
                     #:unless (spurious? G σ Γ W))
           (case V
             [(undefined) ; FIXME hack
              (cond
                [(hash-has-key? 𝒳 x) As]
                [else
                 (set-add As (-A Γ (-blm 'TODO 'Λ (-st-p (-struct-info (-id 'defined 'Λ) 1 ∅)) (list 'undefined))))])]
             [else (set-add As (-A Γ W))])))
       (values ⊥σ As ∅))]
    [(and ref (-ref (and id (-id name l-from)) l-ctx pos))
     (λ (G σ ρ Γ 𝒳)
       (cond
         [(equal? l-from l-ctx)
          (define As
            (for/set: : (℘ -A) ([V (σ@ σ (-α.def id))])
              (define s (if (-o? V) V ref))
              (-A Γ (-W (list V) s))))
          (values ⊥σ As ∅)]
         [else
          (define Vs (σ@ σ (-α.def id)))
          (define Cs (σ@ σ (-α.ctc id)))
          (printf "TODO: monitor value at module 'provide' time instead~n")
          (define As
            (for/set: : (℘ -A) ([V (σ@ σ (-α.def id))])
              (define s (if (-o? V) V ref))
              (-A Γ (-W (list V) s))))
          (values ⊥σ As ∅)]))]
    [(-@ f xs l)
     ((↝.@ '() (map ⇓ xs) l) (⇓ f))]
    [(-if e₀ e₁ e₂)
     ((↝.if (⇓ e₁) (⇓ e₂)) (⇓ e₀))]
    [(-wcm k v b)
     (error '⇓ "TODO: wcm")]
    [(-begin es)
     (match es
       [(cons e* es*) ((↝.begin (map ⇓ es*)) (⇓ e*))]
       [_ ⟦void⟧])]
    [(-begin0 e₀ es)
     ((↝.begin0.v (map ⇓ es)) (⇓ e₀))]
    [(-quote q)
     (cond
       [(Base? q)
        (define b (-b q))
        (λ (G σ ρ Γ 𝒳)
          (values ⊥σ {set (-A Γ (-W (list b) b))} ∅))]
       [else (error '⇓ "TODO: (quote ~a)" q)])]
    [(-let-values bnds bod l)
     (define ⟦bod⟧ (⇓ bod))
     (define xs-⟦e⟧s
       (for/list : (Listof (Pairof (Listof Symbol) -⟦e⟧)) ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (cons xs (⇓ eₓ))))
     (match xs-⟦e⟧s 
       ['() ⟦bod⟧]
       [(cons (cons xs₀ ⟦e⟧₀) xs-⟦eₓ⟧s*)
        ((↝.let-values '() xs₀ xs-⟦eₓ⟧s* ⟦bod⟧ l) ⟦e⟧₀)])]
    [(-letrec-values bnds bod l)
     (define ⟦bod⟧ (⇓ bod))
     (define xs-⟦e⟧s
       (for/list : (Listof (Pairof (Listof Symbol) -⟦e⟧)) ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (cons xs (⇓ eₓ))))
     (match xs-⟦e⟧s
       ['() ⟦bod⟧]
       [(cons (cons xs₀ ⟦e⟧₀) xs-⟦e⟧s*)
        (define all-xs (for*/set: : (℘ Symbol) ([xs-⟦e⟧ xs-⟦e⟧s] [x (car xs-⟦e⟧)]) x))
        (λ (G σ ρ Γ 𝒳)
          (define-values (δσ ρ*)
            (for*/fold ([δσ : -Δσ ⊥σ] [ρ : -ρ ρ]) ([x all-xs])
              (define α (-α.x x Γ))
              (values (⊔ δσ α 'undefined) (hash-set ρ x α))))
          (define σ* (⊔/m σ δσ))
          (((↝.letrec-values all-xs ρ* xs₀ xs-⟦e⟧s* ⟦bod⟧ l) ⟦e⟧₀) G σ* ρ* Γ 𝒳))])]
    [(-set! x e*) ((↝.set! x) (⇓ e*))]
    [(-@-havoc (-x x)) (↝.havoc x)]
    [(-amb es)
     (define ⟦e⟧s (set-map es ⇓))
     (λ (G σ ρ Γ 𝒳)
       (for*/ans ([⟦e⟧ ⟦e⟧s]) (⟦e⟧ G σ ρ Γ 𝒳)))]
    [(-μ/c x c) ((↝.μ/c x) (⇓ c))]
    [(-->i doms rst rng pos)
     (define ⟦rng⟧ (⇓ rng))
     (define ⟦rst⟧
       (match rst
         [(cons x c) (cons x (⇓ c))]
         [#f #f]))
     (define ⟦dom⟧s
       (for/list : (Listof (Pairof Symbol -⟦e⟧)) ([dom doms])
         (match-define (cons x c) dom)
         (cons x (⇓ c))))

     (when ⟦rng⟧
       (printf "ignore #:rest arg for now~n"))

     (match ⟦dom⟧s
       [(cons (cons x ⟦c⟧) ⟦dom⟧s*)
        (λ (G σ ρ Γ 𝒳)
          (((↝.-->i '() x ⟦dom⟧s* ⟦rng⟧ rng ρ pos) ⟦c⟧) G σ ρ Γ 𝒳))]
       [_
        (define d (-?->i '() '() rng))
        (λ (G σ ρ Γ 𝒳)
          (define D (-=>i '() #f ⟦rng⟧ ρ))
          (values ⊥σ {set (-A Γ (-W (list D) d))} ∅))])]
    [(-x/c x)
     (λ (G σ ρ Γ 𝒳)
       (define As
         (for/set: : (℘ -A) ([V (σ@ σ (-α.x/c x))])
           (-A Γ (-W (list V) e))))
       (values ⊥σ As ∅))]
    [(-struct/c si cs pos)
     (match cs
       ['()
        (λ (G σ ρ Γ 𝒳)
          (define V (-St/C #t si '()))
          (define W (-W (list V) e))
          (values ⊥σ {set (-A Γ W)} ∅))]
       [(cons c cs*)
        ((↝.struct/c si '() (map ⇓ cs*) pos) (⇓ c))])]))

(: ℰ⟦_⟧ : -ℰ (℘ -A) → -⟦e⟧)
;; Plug results `As` into hole `ℰ` and resume computation
;; Stacks `ℰ` are also finite, but I can't "compile" them ahead of time because they depend on
;; "run-time" `V`. Using functions instead of flat values to represent `ℰ` may generate
;; infinitely many equivalent but distinct (Racket-level) functions.
;; Memoization might help, but I doubt it speeds up anything.
;; So I'll keep things simple for now.
(define (ℰ⟦_⟧ ℰ As)
  (let go ([ℰ : -ℰ ℰ])
    (match ℰ
      ;; Hacky forms
      [(-ℰₚ.modules ℰ* ⟦m⟧s ⟦e⟧) ((↝.modules ⟦m⟧s ⟦e⟧) (go ℰ*))]
      [(-ℰ.def m xs ℰ*) ((↝.def m xs) (go ℰ*))]
      [(-ℰ.dec id ℰ*) ((↝.dec id) (go ℰ*))]
      ;; Regular forms
      ['□ (λ _ (values ⊥σ As ∅))]
      [(-ℰ.if ℰ* ⟦e₁⟧ ⟦e₂⟧) ((↝.if ⟦e₁⟧ ⟦e₂⟧) (go ℰ*))]
      [(-ℰ.@ WVs ℰ* ⟦e⟧s loc) ((↝.@ WVs ⟦e⟧s loc) (go ℰ*))]
      [(-ℰ.begin ℰ* ⟦e⟧s) ((↝.begin ⟦e⟧s) (go ℰ*))]
      [(-ℰ.begin0.v ℰ* ⟦e⟧s) ((↝.begin0.v ⟦e⟧s) (go ℰ*))]
      [(-ℰ.begin0.e W ℰ* ⟦e⟧s) ((↝.begin0.e W ⟦e⟧s) (go ℰ*))]
      [(-ℰ.let-values xs-Ws (cons xs ℰ*) xs-⟦e⟧s ⟦e⟧ l)
       ((↝.let-values xs-Ws xs xs-⟦e⟧s ⟦e⟧ l) (go ℰ*))]
      [(-ℰ.set! x ℰ*) ((↝.set! x) (go ℰ*))]
      [(-ℰ.μ/c x ℰ*) ((↝.μ/c x) (go ℰ*))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: collect : -M -Ξ -ℬ → -Δσ (℘ -A) (℘ -ℐ) → (Values -ΔM -ΔΞ -Δσ))
;; Collect evaluation results into store deltas
(define ((collect M Ξ ℬ) δσ As ℐs)
  
  (define δM : -ΔM
    (let ([ΔAs (set-subtract As (m@ M ℬ))])
      (if (set-empty? ΔAs) ⊥M (hash ℬ ΔAs))))
  
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
  (λ (G σ ρ Γ 𝒳)
    (values ⊥σ {set (-A Γ W)} ∅)))

(define ⟦void⟧ (⇓const (void)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (ev₁ [e : -e])
  (define-values (δM δΞ δσ) (ev ⊥M ⊥Ξ ⊥σ (-ℬ (⇓ e) ⊥ρ)))
  (values (show-M δM) (show-Ξ δΞ) (show-σ δσ)))
