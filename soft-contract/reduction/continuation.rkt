#lang typed/racket/base

;; Each function `↝._` implements semantics of corresponding continuation frame,
;; returning ⟦e⟧→⟦e⟧.
;; This is factored out because it's used in both compilation `⇓` and resumption `ℰ⟦_⟧`.

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "../proof-relation/main.rkt" "../delta.rkt")

(: ↝.modules : (Listof -⟦e⟧) -⟦e⟧ → -⟦e⟧ → -⟦e⟧)
(define ((↝.modules ⟦m⟧s ⟦e⟧) ⟦e⟧*)
  (define ⟦e⟧ₚ
    (match ⟦m⟧s
      [(cons ⟦m⟧ ⟦m⟧s*) ((↝.modules ⟦m⟧s* ⟦e⟧) ⟦m⟧)]
      ['() ⟦e⟧]))
  
  (λ (G σ ρ Γ 𝒳)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰₚ.modules ℰ ⟦m⟧s ⟦e⟧))
      (λ (σ* Γ* Vs s) (⟦e⟧ₚ G σ* ρ Γ* 𝒳)))
     (⟦e⟧* G σ ρ Γ 𝒳))))

(: ↝.def : Adhoc-Module-Path (Listof Symbol) → -⟦e⟧ → -⟦e⟧)
;; Define top-level `xs` to be values from `⟦e⟧`
(define (((↝.def m xs) ⟦e⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.def m xs ℰ))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity (length xs) (m Γ* Vs)
        (define δσ
          (for/fold ([δσ : -Δσ ⊥σ]) ([x xs] [V Vs])
            (define α (-α.def (-id x m)))
            (⊔ δσ α V)))
        (values δσ {set (-A Γ* -Void/W)} ∅))))
    (⟦e⟧ G σ ρ Γ 𝒳)))

(: ↝.dec : -id → -⟦e⟧ → -⟦e⟧)
;; Make `⟦c⟧`. the contract for `id`.
;; TODO: Perform contract checking at this time instead of when referencing `id`
(define (((↝.dec id) ⟦c⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.dec id ℰ))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ((-id-ctx id) Γ* Vs)
        (match-define (list V) Vs)
        (values (⊔ ⊥σ (-α.ctc id) V) {set (-A Γ* -Void/W)} ∅))))
   (⟦c⟧ G σ ρ Γ 𝒳)))

(: ↝.if : -⟦e⟧ -⟦e⟧ → -⟦e⟧ → -⟦e⟧)
(define (((↝.if ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.if ℰ ⟦e₁⟧ ⟦e₂⟧))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define-values (Γ₁ Γ₂) (Γ+/-V G σ* Γ* V s))
        (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ G σ* ρ Γ* 𝒳))
               (with-Γ Γ₂ (⟦e₂⟧ G σ* ρ Γ* 𝒳))))))
    (⟦e₀⟧ G σ ρ Γ 𝒳)))

(: ↝.@ : (Listof -W¹) (Listof -⟦e⟧) -src-loc → -⟦e⟧ → -⟦e⟧)
(define (((↝.@ Ws ⟦e⟧s loc) ⟦e⟧) G σ ρ Γ 𝒳)

  (define l (-src-loc-party loc))

  (define cont : (-σ -Γ -W¹ → (Values -Δσ (℘ -A) (℘ -ℐ)))
    (match ⟦e⟧s
      [(cons ⟦e⟧* ⟦e⟧s*)
       (λ (σ* Γ* W)
         (((↝.@ (cons W Ws) ⟦e⟧s* loc) ⟦e⟧*) G σ* ρ Γ* 𝒳))]
      [_
       (λ (σ* Γ* W)
         (match-define (cons W-f W-xs) (reverse (cons W Ws)))
         (ap G σ* Γ* 𝒳 W-f W-xs loc))]))

  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.@ Ws ℰ ⟦e⟧s loc))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 (l Γ* Vs)
        (match-define (list V) Vs)
        (cont σ* Γ* (-W¹ V s)))))
   (⟦e⟧ G σ ρ Γ 𝒳)))

(: ↝.begin : (Listof -⟦e⟧) → -⟦e⟧ → -⟦e⟧)
(define ((↝.begin ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    [(cons ⟦e⟧* ⟦e⟧s*)
     (define ⟦eᵣ⟧ ((↝.begin ⟦e⟧s*) ⟦e⟧*))
     (λ (G σ ρ Γ 𝒳)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin ℰ ⟦e⟧s))
         (λ (σ* Γ* Vs s) (⟦eᵣ⟧ G σ* ρ Γ* 𝒳)))
        (⟦e⟧ G σ ρ Γ 𝒳)))]
    [_ ⟦e⟧]))

(: ↝.begin0.v : (Listof -⟦e⟧) → -⟦e⟧ → -⟦e⟧)
;; Waiting on `⟦e⟧` to be the returned value for `begin0`
(define ((↝.begin0.v ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    [(cons ⟦e⟧* ⟦e⟧s*)
     (λ (G σ ρ Γ 𝒳)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin0.v ℰ ⟦e⟧s))
         (λ (σ* Γ* Vs s)
           (define ⟦eᵣ⟧ ((↝.begin0.e (-W Vs s) ⟦e⟧s*) ⟦e⟧*))
           (⟦eᵣ⟧ G σ* ρ Γ* 𝒳)))
        (⟦e⟧ G σ ρ Γ 𝒳)))]
    ['() ⟦e⟧]))

(: ↝.begin0.e : -W (Listof -⟦e⟧) → -⟦e⟧ → -⟦e⟧)
(define (((↝.begin0.e W ⟦e⟧s) ⟦e⟧) G σ ρ Γ 𝒳)
  (match ⟦e⟧s
    [(cons ⟦e⟧* ⟦e⟧s*)
     (apply/values
      (acc
       σ
       (λ (ℰ) (-ℰ.begin0.e W ℰ ⟦e⟧s))
       (λ (σ* Γ* Vs s)
         (((↝.begin0.e W ⟦e⟧s*) ⟦e⟧*) G σ* ρ Γ* 𝒳)))
      (⟦e⟧ G σ ρ Γ 𝒳))]
    ['() (values ⊥σ {set (-A Γ W)} ∅)]))

(: ↝.let-values : (Listof (Pairof Symbol -W¹))
                  (Listof Symbol)
                  (Listof (Pairof (Listof Symbol) -⟦e⟧))
                  -⟦e⟧
                  Mon-Party
                  → -⟦e⟧ → -⟦e⟧)
(define (((↝.let-values x-Ws xs xs-⟦e⟧s ⟦e⟧ l) ⟦eₓ⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.let-values x-Ws (cons xs ℰ) xs-⟦e⟧s ⟦e⟧ l))
    (λ (σ* Γ* Vs s)
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
        (match xs-⟦e⟧s
          [(cons (cons xs* ⟦e⟧*) xs-⟦e⟧s*)
           (((↝.let-values x-Ws* xs* xs-⟦e⟧s* ⟦e⟧ l) ⟦e⟧*) G σ* ρ Γ* 𝒳)]
          ['()
           (define-values (ρ* δσ 𝒳*)
             (for/fold ([ρ* : -ρ ρ] [δσ : -Δσ ⊥σ] [𝒳* : -𝒳 𝒳]) ([x-W x-Ws*])
               (match-define (cons x (-W¹ V s)) x-W)
               (define α (-α.x x Γ))
               (define 𝒳** (if s (hash-set 𝒳* x s) 𝒳*))
               (values (hash-set ρ* x α) (⊔ δσ α V) 𝒳**)))
           (define σ** (⊔/m σ* δσ))
           (⊔/ans (values δσ ∅ ∅) (⟦e⟧ G σ** ρ* Γ* 𝒳*))]))))
   (⟦eₓ⟧ G σ ρ Γ 𝒳)))

(: ↝.set! : Symbol → -⟦e⟧ → -⟦e⟧)
(define (((↝.set! x) ⟦e⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.set! x ℰ))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (values (⊔ ⊥σ (ρ@ ρ x) V) {set (-A Γ* -Void/W)} ∅))))
   (⟦e⟧ G σ ρ Γ 𝒳)))

(: ↝.μ/c : Integer → -⟦e⟧ → -⟦e⟧)
(define (((↝.μ/c x) ⟦c⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.μ/c x ℰ))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (values ⊥σ {set (-A Γ* (-W Vs s))} ∅))))
   (⟦c⟧ G σ ρ Γ 𝒳)))

(: ↝.havoc : Symbol → -⟦e⟧)
(define ((↝.havoc x) G σ ρ Γ 𝒳)
  (define Vs (σ@ σ (ρ@ ρ x)))
  (error '↝.havoc "TODO"))

(: ↝.struct/c : -struct-info (Listof -W¹) (Listof -⟦e⟧) Integer → -⟦e⟧ → -⟦e⟧)
(define (((↝.struct/c si Ws ⟦c⟧s pos) ⟦c⟧) G σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.struct/c si Ws ℰ ⟦c⟧s pos))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define Ws* (cons (-W¹ V s) Ws))
        (match ⟦c⟧s
          [(cons ⟦c⟧* ⟦c⟧s*)
           (((↝.struct/c si Ws* ⟦c⟧s* pos) ⟦c⟧*) G σ* ρ Γ* 𝒳)]
          ['()
           (define-values (δσ αs cs flat?) ; αs reverses Ws, which is reversed
             (for/fold ([δσ : -Δσ ⊥σ] [αs : (Listof -α.struct/c) '()]
                        [cs : (Listof -s) '()] [flat? : Boolean #t])
                       ([(W i) (in-indexed Ws*)])
               (match-define (-W¹ C c) W)
               (define α (-α.struct/c (list (-struct-info-id si) pos i)))
               (values (⊔ δσ α C) (cons α αs) (cons c cs) (and flat? (C-flat? C)))))
           (define V (-St/C flat? si αs))
           (values δσ {set (-A Γ (-W (list V) (-?struct/c si cs)))} ∅)]))))
   (⟦c⟧ G σ ρ Γ 𝒳)))

(: ap : -G -σ -Γ -𝒳 -W¹ (Listof -W¹) -src-loc → (Values -Δσ (℘ -A) (℘ -ℐ)))
;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define (ap G σ Γ 𝒳 Wₕ Wₓs loc)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))

  ;; TODO: guard against wrong arity

  ;; Apply primitive
  (define (ap/δ [o : Symbol])
    (define-values (δσ A*) (δ G σ Γ o Wₓs loc))
    (match-define (-A* Γₐ res) A*)
    (define Wₐ (if (list? res) (-W res (apply -?@ o sₓs)) res))
    (values δσ {set (-A Γₐ Wₐ)} ∅))

  ;; Apply λ abstraction
  (define (ap/β [xs : -formals] [⟦e⟧ : -⟦e⟧] [ρ : -ρ])
    (define-values (δσ ρ*)
      (match xs
        [(? list? xs)
         (for/fold ([δσ : -Δσ ⊥σ] [ρ* : -ρ ρ]) ([x xs] [V Vₓs])
           (define α (-α.x x Γ))
           (values (⊔ δσ α V) (ρ+ ρ* x α)))]
        [_ (error 'ap "TODO: varargs")]))
    (define bnds (map (inst cons Symbol -s) xs sₓs))
    (values δσ ∅ {set (-ℐ (-ℋ Γ 𝒳 sₕ bnds '□) (-ℬ ⟦e⟧ ρ*))}))
  
  (match Vₕ
    [(-Clo xs ⟦e⟧ ρ) (ap/β xs ⟦e⟧ ρ)]
    [(? symbol? o) (ap/δ o)]
    [(-Ar (-=>i doms rst ⟦d⟧ ρ) (cons α s-g) l³)
     (error "TODO")]
    [(-And/C #t α₁ α₂)
     (error "TODO")]
    [(-Or/C #t α₁ α₂)
     (error "TODO")]
    [(-Not/C α)
     (error "TODO")]
    [(-St/C #t si αs)
     (error "TODO")]
    [(-●)
     (error "TODO")]
    [_ (values ⊥σ {set (-A Γ (-blm (-src-loc-party loc) 'Λ 'procedure? (list Vₕ)))} ∅)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: acc : -σ (-ℰ → -ℰ) (-σ -Γ (Listof -V) -s → (Values -Δσ (℘ -A) (℘ -ℐ))) →
                 -Δσ (℘ -A) (℘ -ℐ) → (Values -Δσ (℘ -A) (℘ -ℐ)))
(define ((acc σ f comp) δσ As ℐs)
  (define-values (Vs Es) (set-partition -A/V? As))
  (define ℐs*
    (map/set
     (match-lambda
       [(-ℐ (-ℋ Γ 𝒳 s 𝒳*    ℰ ) ℬ)
        (-ℐ (-ℋ Γ 𝒳 s 𝒳* (f ℰ)) ℬ)])
     ℐs))
  (define σ* (⊔/m σ δσ))
  (for/fold ([δσ : -Δσ δσ] [As : (℘ -A) Es] [ℐs : (℘ -ℐ) ℐs*])
            ([A Vs])
    (match-define (-A Γ* (-W Vs s)) A)
    (define-values (δσ+ As+ ℐs+) (comp σ* Γ* Vs s))
    (values (⊔/m δσ δσ+) (∪ As As+) (∪ ℐs ℐs+))))

(define-syntax-rule (with-guarded-arity n* (l Γ Vs) e ...)
  (let ([n n*]
        [m (length Vs)])
    (cond
      [(= n m) e ...]
      [else
       (define C #|HACK|# (string->symbol (format "~a value(s)" n)))
       (values ⊥σ {set (-A Γ (-blm l 'Λ C Vs))} ∅)])))
