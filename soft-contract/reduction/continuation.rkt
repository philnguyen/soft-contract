#lang typed/racket/base

;; Each function `↝._` implements semantics of corresponding continuation frame,
;; returning ⟦e⟧→⟦e⟧.
;; This is factored out because it's used in both compilation `⇓` and resumption `ℰ⟦_⟧`.

(provide (all-defined-out))

(require
 racket/match racket/set racket/list
 "../utils/main.rkt" "../ast/main.rkt" "../runtime/main.rkt" "../proof-relation/main.rkt" "../delta.rkt")

(: ↝.modules : (Listof -⟦e⟧) -⟦e⟧ → -⟦ℰ⟧)
(define ((↝.modules ⟦m⟧s ⟦e⟧) ⟦e⟧ᵢ)
  (define ⟦e⟧ᵣ
    (match ⟦m⟧s
      ['() ⟦e⟧]
      [(cons ⟦m⟧ ⟦m⟧s*) ((↝.modules ⟦m⟧s* ⟦e⟧) ⟦m⟧)]))
  
  (λ (M σ ℬ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰₚ.modules ℰ ⟦m⟧s ⟦e⟧))
      (λ (σ* Γ* W) (⟦e⟧ᵣ M σ* (-ℬ-with-Γ ℬ Γ*))))
     (⟦e⟧ᵢ M σ ℬ))))


(: ↝.def : Adhoc-Module-Path (Listof Symbol) → -⟦ℰ⟧)
;; Define top-level `xs` to be values from `⟦e⟧`
(define (((↝.def m xs) ⟦e⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.def m xs ℰ))
    (λ (σ* Γ* W)
      (define Vs (-W-Vs W))
      (with-guarded-arity (length xs) (m Γ* Vs)
        (define δσ
          (for/fold ([δσ : -Δσ ⊥σ]) ([x xs] [V Vs])
            (define α (-α.def (-id x m)))
            (⊔ δσ α V)))
        (values δσ {set (-ΓW Γ* -Void/W)} ∅ ∅))))
    (⟦e⟧ M σ ℬ)))

(: ↝.dec : -id → -⟦ℰ⟧)
;; Make `⟦c⟧`. the contract for `id`.
;; TODO: Perform contract checking at this time instead of when referencing `id`
(define (((↝.dec id) ⟦c⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.dec id ℰ))
    (λ (σ* Γ* W)
      (define Vs (-W-Vs W))
      (with-guarded-arity 1 ((-id-ctx id) Γ* Vs)
        (match-define (list V) Vs)
        (values (⊔ ⊥σ (-α.ctc id) V) {set (-ΓW Γ* -Void/W)} ∅ ∅))))
   (⟦c⟧ M σ ℬ)))

(: ↝.if : -⟦e⟧ -⟦e⟧ → -⟦ℰ⟧)
(define (((↝.if ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.if ℰ ⟦e₁⟧ ⟦e₂⟧))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define-values (Γ₁ Γ₂) (Γ+/-V M σ* Γ* V s))
        (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ M σ* (-ℬ-with-Γ ℬ Γ₁)))
               (with-Γ Γ₂ (⟦e₂⟧ M σ* (-ℬ-with-Γ ℬ Γ₂)))))))
    (⟦e₀⟧ M σ ℬ)))

(: ↝.@ : (Listof -W¹) (Listof -⟦e⟧) -src-loc → -⟦ℰ⟧)
(define (((↝.@ Ws ⟦e⟧s loc) ⟦e⟧) M σ ℬ)

  (define l (-src-loc-party loc))

  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.@ Ws ℰ ⟦e⟧s loc))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 (l Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (define ℬ* (-ℬ-with-Γ ℬ Γ*))
        (match ⟦e⟧s ; TODO: move this dispatch out?
          ['()
           (match-define (cons Wₕ Wₓs) (reverse Ws*))
           (ap M σ* ℬ* Wₕ Wₓs loc)]
          [(cons ⟦e⟧* ⟦e⟧s*)
           (((↝.@ Ws* ⟦e⟧s* loc) ⟦e⟧*) M σ* ℬ*)]))))
   (⟦e⟧ M σ ℬ)))

(: ↝.begin : (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.begin ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['() ⟦e⟧]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (define ⟦eᵣ⟧ ((↝.begin ⟦e⟧s*) ⟦e⟧*))
     (λ (M σ ℬ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin ℰ ⟦e⟧s))
         (λ (σ* Γ* _) (⟦eᵣ⟧ M σ* (-ℬ-with-Γ ℬ Γ*))))
        (⟦e⟧ M σ ℬ)))]))

(: ↝.begin0.v : (Listof -⟦e⟧) → -⟦ℰ⟧)
;; Waiting on `⟦e⟧` to be the returned value for `begin0`
(define ((↝.begin0.v ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['() ⟦e⟧]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (λ (M σ ℬ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin0.v ℰ ⟦e⟧s))
         (λ (σ* Γ* W)
           (define ⟦eᵣ⟧ ((↝.begin0.e W ⟦e⟧s*) ⟦e⟧*))
           (⟦eᵣ⟧ M σ* (-ℬ-with-Γ ℬ Γ*))))
        (⟦e⟧ M σ ℬ)))]))

(: ↝.begin0.e : -W (Listof -⟦e⟧) → -⟦ℰ⟧)
(define ((↝.begin0.e W ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    ['()
     (λ (M σ ℬ)
       (values ⊥σ {set (-ΓW (-ℬ-cnd ℬ) W)} ∅ ∅))]
    [(cons ⟦e⟧* ⟦e⟧s*)
     (define ⟦e⟧ᵣ ((↝.begin0.e W ⟦e⟧s*) ⟦e⟧*))
     (λ (M σ ℬ)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin0.e W ℰ ⟦e⟧s))
         (λ (σ* Γ* _)
           (⟦e⟧ᵣ M σ* (-ℬ-with-Γ ℬ Γ*))))
        (⟦e⟧ M σ ℬ)))]))

(: ↝.let-values : (Listof (Pairof Symbol -W¹))
                  (Listof Symbol)
                  (Listof (Pairof (Listof Symbol) -⟦e⟧))
                  -⟦e⟧
                  Mon-Party
                  → -⟦ℰ⟧)
(define (((↝.let-values x-Ws xs xs-⟦e⟧s ⟦e⟧ l) ⟦eₓ⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.let-values x-Ws (cons xs ℰ) xs-⟦e⟧s ⟦e⟧ l))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (define n (length xs))
      (with-guarded-arity n (l Γ* Vs)
        (define x-Ws*
          (foldr
           (λ ([x : Symbol] [V : -V] [s : -s] [x-Ws* : (Listof (Pairof Symbol -W¹))])
             (cons (cons x (-W¹ V s)) x-Ws*))
           x-Ws
           xs
           Vs
           (split-values s n)))
        (match xs-⟦e⟧s ; TODO dispatch outside?
          ['()
           (match-define (-ℬ ⟦e⟧₀ ρ _ 𝒞) ℬ)
           (define-values (ρ* δσ Γ**)
             (for/fold ([ρ* : -ρ ρ] [δσ : -Δσ ⊥σ] [Γ** : -Γ Γ*])
                       ([x-W x-Ws*])
               (match-define (cons x (-W¹ V s)) x-W)
               (define α (-α.x x 𝒞))
               (values (hash-set ρ* x α)
                       (⊔ δσ α V)
                       (-Γ-with-aliases Γ* x s))))
           (define σ** (⊔/m σ* δσ))
           (⊔/ans (values δσ ∅ ∅ ∅)
                  (⟦e⟧ M σ** (-ℬ ⟦e⟧₀ ρ* Γ** 𝒞)))]
          [(cons (cons xs* ⟦e⟧*) xs-⟦e⟧s*)
           (((↝.let-values x-Ws* xs* xs-⟦e⟧s* ⟦e⟧ l) ⟦e⟧*) M σ* (-ℬ-with-Γ ℬ Γ*))]
          ))))
   (⟦eₓ⟧ M σ ℬ)))

(: ↝.letrec-values : -Δρ
                     (Listof Symbol)
                     (Listof (Pairof (Listof Symbol) -⟦e⟧))
                     -⟦e⟧
                     Mon-Party
                     → -⟦ℰ⟧)
(define (((↝.letrec-values δρ xs xs-⟦e⟧s ⟦e⟧ l) ⟦eₓ⟧) M σ ℬ)
  ;; FIXME: inefficient. `ρ*` is recomputed many times
  (define ρ (-ℬ-env ℬ))
  (define ℬ* (-ℬ-with-ρ ℬ (ρ++ ρ δρ)))
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.letrec-values δρ (cons xs ℰ) xs-⟦e⟧s ⟦e⟧ l))
    (λ (σ₀ Γ₀ W)
      (define n (length xs))
      (match-define (-W Vs s) W)
      (with-guarded-arity n (l Γ₀ Vs)
        ;; Update/widen store and path condition
        (define-values (δσ Γ₁)
          (for/fold ([δσ : -Δσ ⊥σ] [Γ₁ : -Γ Γ₀])
                    ([x xs] [V Vs] [sₓ (split-values s n)])
            (values (⊔ δσ (ρ@ δρ x) V)
                    (if sₓ (-Γ-with-aliases Γ₁ x sₓ) Γ₁))))
        (define σ₁ (⊔/m σ₀ δσ))
        
        (match xs-⟦e⟧s
          [(cons (cons xs* ⟦e⟧*) xs-⟦e⟧s*)
           (⊔/ans
             (values δσ ∅ ∅ ∅)
             (((↝.letrec-values δρ xs* xs-⟦e⟧s* ⟦e⟧ l) ⟦e⟧*) M σ₁ (-ℬ-with-Γ ℬ Γ₁)))]
          ['()
           (define-values (δσ* ΓWs ΓEs ℐs) (⟦e⟧ M σ (-ℬ-with-Γ ℬ* Γ₁)))
           
           ;;; Erase irrelevant part of path conditions after executing letrec body

           ;; Free variables that outside of `letrec` understands
           (define xs₀ (list->set (hash-keys ρ)))

           (: trim-s : -s → -s)
           ;; Only keep symbol if it still make sense out of `letrec`'s scope
           (define (trim-s s)
             (and s (⊆ (fv s) xs₀) s))

           (: trim-Γ : -Γ → -Γ)
           ;; Only keep facts that still make sense out of `letrec`'s scope
           (define (trim-Γ Γ)
             (match-define (-Γ φs as γs) Γ₁)
             (define φs*
               (for*/set: : (℘ -e) ([φ φs] [φ* (in-value (trim-s φ))] #:when φ*)
                 φ*))
             (define as*
               (for/hash : (HashTable Symbol -e) ([(x e) as] #:when (∋ xs₀ x))
                 (values x e)))
             (define γs*
               (for*/set: : (℘ -γ) ([γ γs]
                                    #:when (trim-s (-γ-fun γ))
                                    #:when
                                    (for/and : Boolean ([p (-γ-param->arg γ)])
                                      (and (trim-s (cdr p)) #t))) ; force boolean :(
                 γ))
             (-Γ φs* as* γs*))
             
           (define ΓWs*
             (map/set
              (match-lambda
                [(-ΓW Γ (-W Vs s))
                 (-ΓW (trim-Γ Γ) (-W Vs (trim-s s)))])
              ΓWs))
           
           (define ΓEs*
             (map/set
              (match-lambda
                [(-ΓE Γ blm)
                 (-ΓE (trim-Γ Γ) blm)])
              ΓEs))
           
           (define ℐs*
             (map/set
              (match-lambda
                [(-ℐ (-ℋ Γ f bnds ℰ) ℬ)
                 (define Γ* (trim-Γ Γ))
                 (define f* (trim-s f))
                 (define bnds*
                   (for/list : (Listof (Pairof Symbol -s)) ([bnd bnds])
                     (match-define (cons x s) bnd)
                     (cons x (trim-s s))))
                 (-ℐ (-ℋ Γ* f* bnds* ℰ) ℬ)])
             ℐs))
           
           (values (⊔/m δσ δσ*) ΓWs* ΓEs* ℐs*)]))))
   (⟦eₓ⟧ M σ ℬ*)))

(: ↝.set! : Symbol → -⟦ℰ⟧)
(define (((↝.set! x) ⟦e⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.set! x ℰ))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define α (ρ@ (-ℬ-env ℬ) x))
        (values (⊔ ⊥σ α V) {set (-ΓW Γ* -Void/W)} ∅ ∅))))
   (⟦e⟧ M σ ℬ)))

(: ↝.μ/c : Integer → -⟦ℰ⟧)
(define (((↝.μ/c x) ⟦c⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.μ/c x ℰ))
    (λ (σ* Γ* W)
      (with-guarded-arity 1 ('TODO Γ* (-W-Vs W))
        (values ⊥σ {set (-ΓW Γ* W)} ∅ ∅))))
   (⟦c⟧ M σ ℬ)))

(: ↝.-->i : (Listof -W¹) (Listof -⟦e⟧) -⟦e⟧ Integer → -⟦ℰ⟧)
(define (((↝.-->i Ws ⟦c⟧s ⟦mk-d⟧ l) ⟦e⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.-->i Ws ℰ ⟦c⟧s ⟦mk-d⟧ l))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (match ⟦c⟧s
          [(cons ⟦c⟧ ⟦c⟧s*)
           (((↝.-->i Ws* ⟦c⟧s* ⟦mk-d⟧ l) ⟦c⟧) M σ* (-ℬ-with-Γ ℬ Γ*))]
          ['()
           (define-values (δσ αs cs) ; `αs` and `cs` reverses `Ws*`, which is reversed
             (for/fold ([δσ : -Δσ ⊥σ] [αs : (Listof -α.dom) '()] [cs : (Listof -s) '()])
                       ([(W i) (in-indexed Ws*)])
               (match-define (-W¹ C c) W)
               (define α (-α.dom (cons l i)))
               (values (⊔ δσ α C) (cons α αs) (cons c cs))))
           
           (define ℬ* (-ℬ-with-Γ ℬ Γ*))
           (define-values (_δσ ΓClos _ΓEs _ℐs) (⟦mk-d⟧ M σ* ℬ*))
           (begin ; `⟦mk-d⟧` should only be a λ!!
             (assert (= 0 (hash-count _δσ)))
             (assert (set-empty? _ΓEs))
             (assert (set-empty? _ℐs))
             (assert (= 1 (set-count ΓClos))))
           (match-define (-ΓW Γ** (-W (list (? -Clo? Mk-D)) mk-d)) ΓClos)
           (define C (-=>i αs Mk-D))
           (define c (-?->i cs mk-d))
           (values δσ {set (-ΓW Γ** (-W (list C) c))} ∅ ∅)]))))
   (⟦e⟧ M σ ℬ)))

(: ↝.havoc : Symbol → -⟦e⟧)
(define ((↝.havoc x) M σ ℬ)
  (define Vs (σ@ σ (ρ@ (-ℬ-env ℬ) x)))
  (error '↝.havoc "TODO"))

(: ↝.struct/c : -struct-info (Listof -W¹) (Listof -⟦e⟧) Integer → -⟦ℰ⟧)
(define (((↝.struct/c si Ws ⟦c⟧s l) ⟦c⟧) M σ ℬ)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.struct/c si Ws ℰ ⟦c⟧s l))
    (λ (σ* Γ* W)
      (match-define (-W Vs s) W)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (match ⟦c⟧s
          [(cons ⟦c⟧* ⟦c⟧s*)
           (((↝.struct/c si Ws* ⟦c⟧s* l) ⟦c⟧*) M σ* (-ℬ-with-Γ ℬ Γ*))]
          ['()
           (define-values (δσ αs cs flat?) ; `αs` and `cs` reverse `Ws`, which is reversed
             (for/fold ([δσ : -Δσ ⊥σ]
                        [αs : (Listof -α.struct/c) '()]
                        [cs : (Listof -s) '()]
                        [flat? : Boolean #t])
                       ([(W i) (in-indexed Ws*)])
               (match-define (-W¹ C c) W)
               (define α (-α.struct/c (list (-struct-info-id si) l i)))
               (values (⊔ δσ α C) (cons α αs) (cons c cs) (and flat? (C-flat? C)))))
           (define V (-St/C flat? si αs))
           (values δσ {set (-ΓW Γ* (-W (list V) (-?struct/c si cs)))} ∅ ∅)]))))
   (⟦c⟧ M σ ℬ)))

(: ap : -M -σ -ℬ -W¹ (Listof -W¹) -src-loc → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define (ap M σ ℬ₀ Wₕ Wₓs loc)
  (match-define (-ℬ ⟦e⟧₀ ρ₀ Γ₀ 𝒞₀) ℬ₀)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ (apply -?@ sₕ sₓs))

  ;; TODO: guard against wrong arity

  (: ap/δ : Symbol → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
  ;; Apply primitive
  (define (ap/δ o)
    (define-values (δσ A*) (δ M σ Γ₀ o Wₓs loc))
    (cond [(list? A*)
           (values δσ {set (-ΓW Γ₀ (-W A* sₐ))} ∅ ∅)]
          ;; Rely on `δ` giving no error
          [else (⊥ans)]))

  (: ap/β : -formals -⟦e⟧ -ρ -Γ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
  ;; Apply λ abstraction
  (define (ap/β xs ⟦e⟧ ρ Γ₁)
    (define 𝒞₁ (𝒞+ 𝒞₀ (cons ⟦e⟧ (-src-loc-pos loc))))
    (define-values (δσ ρ₁)
      (match xs
        [(? list? xs)
         (for/fold ([δσ : -Δσ ⊥σ] [ρ₁ : -ρ ρ])
                   ([x xs] [V Vₓs])
           (define α (-α.x x 𝒞₁))
           (values (⊔ δσ α V) (ρ+ ρ₁ x α)))]
        [_ (error 'ap/β "TODO: varargs")]))
    (define bnds (map (inst cons Symbol -s) xs sₓs))
    (define ℬ₁ (-ℬ ⟦e⟧ ρ₁ Γ₁ 𝒞₁))
    (values δσ ∅ ∅ {set (-ℐ (-ℋ Γ₀ sₕ bnds '□) ℬ₁)}))
  
  (match Vₕ
    [(-Clo xs ⟦e⟧ ρ Γ) (ap/β xs ⟦e⟧ ρ Γ)]
    [(? symbol? o) (ap/δ o)]
    [(-Ar _ _ l³)
     (error 'ap "Arr")]
    [(-And/C #t α₁ α₂)
     (error 'ap "And/C")]
    [(-Or/C #t α₁ α₂)
     (error 'ap "Or/C")]
    [(-Not/C α)
     (error 'ap "Not/C")]
    [(-St/C #t si αs)
     (error 'ap "St/C")]
    [(-●) ; FIXME havoc
     (printf "ap: ●~n")
     (values ⊥σ {set (-ΓW Γ₀ (-W -●/Vs sₐ))} ∅ ∅)]
    [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm (-src-loc-party loc) 'Λ (list 'procedure?) (list Vₕ)))} ∅)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: acc : -σ (-ℰ → -ℰ) (-σ -Γ -W → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
        → -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)
        → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
;; Bind-ish. Takes care of store widening.
;; Caller takes care of stack accumulation and what to do with result.
(define ((acc σ f comp) δσ ΓWs ΓEs ℐs)
  (define ℐs*
    (map/set
     (match-lambda
       [(-ℐ (-ℋ Γ s 𝒳    ℰ ) ℬ)
        (-ℐ (-ℋ Γ s 𝒳 (f ℰ)) ℬ)])
     ℐs))
  (define σ* (⊔/m σ δσ))
  (for/fold ([δσ : -Δσ δσ] [ΓWs* : (℘ -ΓW) ∅] [ΓEs* : (℘ -ΓE) ΓEs] [ℐs* : (℘ -ℐ) ℐs*])
            ([ΓW ΓWs])
    (match-define (-ΓW Γ* W) ΓW)
    (define-values (δσ+ ΓWs+ ΓEs+ ℐs+) (comp σ* Γ* W))
    (values (⊔/m δσ δσ+) (∪ ΓWs* ΓWs+) (∪ ΓEs* ΓEs+) (∪ ℐs* ℐs+))))

(define-syntax-rule (with-guarded-arity n* (l Γ Vs) e ...)
  (let ([n n*]
        [m (length Vs)])
    (cond
      [(= n m) e ...]
      [else
       (define Cs (make-list n 'any/c))
       (values ⊥σ ∅ {set (-ΓE Γ (-blm l 'Λ Cs Vs))} ∅)])))
