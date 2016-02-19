#lang typed/racket/base

;; Each function `↝._` implements semantics of corresponding continuation frame,
;; returning ⟦e⟧→⟦e⟧.
;; This is factored out because it's used in both compilation `⇓` and resumption `ℰ⟦_⟧`.

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "../proof-relation/main.rkt" "../delta.rkt")

(: ↝.modules : (Listof -⟦e⟧) -⟦e⟧ → -⟦e⟧ → -⟦e⟧)
(define (↝.modules ⟦m⟧s ⟦e⟧)
  (define ⟦e⟧ₚ
    (match ⟦m⟧s
      [(cons ⟦m⟧ ⟦m⟧s*) ((↝.modules ⟦m⟧s* ⟦e⟧) ⟦m⟧)]
      ['() ⟦e⟧]))

  (λ (⟦e⟧*)
    (λ (M σ ρ Γ 𝒳)
      (apply/values
       (acc
        σ
        (λ (ℰ) (-ℰₚ.modules ℰ ⟦m⟧s ⟦e⟧))
        (λ (σ* Γ* Vs s) (⟦e⟧ₚ M σ* ρ Γ* 𝒳)))
       (⟦e⟧* M σ ρ Γ 𝒳)))))

(: ↝.def : Adhoc-Module-Path (Listof Symbol) → -⟦e⟧ → -⟦e⟧)
(define (((↝.def m xs) ⟦e⟧) M σ ρ Γ 𝒳)
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
    (⟦e⟧ M σ ρ Γ 𝒳)))

(: ↝.dec : -id → -⟦e⟧ → -⟦e⟧)
(define (((↝.dec id) ⟦c⟧) M σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.dec id ℰ))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ((-id-ctx id) Γ* Vs)
        (match-define (list V) Vs)
        (values (⊔ ⊥σ (-α.ctc id) V) {set (-A Γ* -Void/W)} ∅))))
   (⟦c⟧ M σ ρ Γ 𝒳)))

(: ↝.if : -⟦e⟧ -⟦e⟧ → -⟦e⟧ → -⟦e⟧)
(define (((↝.if ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ρ Γ 𝒳)
  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.if ℰ ⟦e₁⟧ ⟦e₂⟧))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 ('TODO Γ* Vs)
        (match-define (list V) Vs)
        (define-values (Γ₁ Γ₂) (Γ+/-V M σ* Γ* V s))
        (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ M σ* ρ Γ* 𝒳))
               (with-Γ Γ₂ (⟦e₂⟧ M σ* ρ Γ* 𝒳))))))
    (⟦e₀⟧ M σ ρ Γ 𝒳)))

(: ↝.@ : (Listof -W¹) (Listof -⟦e⟧) -src-loc → -⟦e⟧ → -⟦e⟧)
(define (((↝.@ Ws ⟦e⟧s loc) ⟦e⟧) M σ ρ Γ 𝒳)

  (define l (-src-loc-party loc))

  (define cont : (-σ -Γ -W¹ → (Values -Δσ (℘ -A) (℘ -ℐ)))
    (match ⟦e⟧s
      [(cons ⟦e⟧* ⟦e⟧s*)
       (λ (σ* Γ* W)
         (((↝.@ (cons W Ws) ⟦e⟧s* loc) ⟦e⟧*) M σ* ρ Γ* 𝒳))]
      [_
       (λ (σ* Γ* W)
         (match-define (cons W-f W-xs) (reverse (cons W Ws)))
         (ap M σ* Γ* 𝒳 W-f W-xs loc))]))

  (apply/values
   (acc
    σ
    (λ (ℰ) (-ℰ.@ Ws ℰ ⟦e⟧s loc))
    (λ (σ* Γ* Vs s)
      (with-guarded-arity 1 (l Γ* Vs)
        (match-define (list V) Vs)
        (cont σ* Γ* (-W¹ V s)))))
   (⟦e⟧ M σ ρ Γ 𝒳)))

(: ↝.begin : (Listof -⟦e⟧) → -⟦e⟧ → -⟦e⟧)
(define ((↝.begin ⟦e⟧s) ⟦e⟧)
  (match ⟦e⟧s
    [(cons ⟦e⟧* ⟦e⟧s*)
     (λ (M σ ρ Γ 𝒳)
       (apply/values
        (acc
         σ
         (λ (ℰ) (-ℰ.begin ℰ ⟦e⟧s))
         (λ ([σ* : -σ] [Γ* : -Γ] [Vs : (Listof -V)] [s : -s])
           (((↝.begin ⟦e⟧s*) ⟦e⟧*) M σ* ρ Γ* 𝒳)))
        (⟦e⟧ M σ ρ Γ 𝒳)))]
    [_ ⟦e⟧]))

(: ap : -M -σ -Γ -𝒳 -W¹ (Listof -W¹) -src-loc → (Values -Δσ (℘ -A) (℘ -ℐ)))
;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define (ap M σ Γ 𝒳 Wₕ Wₓₛ loc)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓₛ sₓₛ)
    (for/lists ([Vₓₛ : (Listof -V)] [sₓₛ : (Listof -s)])
               ([Wₓ Wₓₛ])
      (match-define (-W¹ V s) Wₓ)
      (values V s)))

  ;; TODO: guard against wrong arity

  ;; Apply primitive
  (define (ap/δ [o : Symbol])
    (define-values (δσ A*) (δ M σ Γ o Wₓₛ loc))
    (match-define (-A* Γₐ res) A*)
    (define Wₐ (if (list? res) (-W res (apply -?@ o sₓₛ)) res))
    (values δσ {set (-A Γₐ Wₐ)} ∅))

  ;; Apply λ abstraction
  (define (ap/β [xs : -formals] [⟦e⟧ : -⟦e⟧] [ρ : -ρ])
    (define-values (δσ ρ*)
      (match xs
        [(? list? xs)
         (for/fold ([δσ : -Δσ ⊥σ] [ρ* : -ρ ρ])
                   ([x xs] [V Vₓₛ])
           (define α (-α.x x Γ))
           (values (⊔ δσ α V) (ρ+ ρ* x α)))]
        [_ (error 'ap "TODO: varargs")]))
    (define 𝒳* (for/hash : -𝒳 ([x xs] [s sₓₛ] #:when s) (values x s)))
    (values δσ ∅ {set (-ℐ (-ℋ Γ 𝒳 sₕ 𝒳* '□) (-ℬ ⟦e⟧ ρ*))}))
  
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
       (values ⊥σ {set (-A Γ (-blm l 'Λ C (list (-b m))))} ∅)])))
