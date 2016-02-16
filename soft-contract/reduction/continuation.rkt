#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/def.rkt" "../utils/set.rkt" "../utils/untyped-macros.rkt" "../utils/map.rkt" "../utils/function.rkt"
 "../ast/definition.rkt"
 "runtime.rkt")

(: ⟦-ℰ.if⟧ : -⟦e⟧ -⟦e⟧ → -⟦ℰ⟧)
(define (((⟦-ℰ.if⟧ ⟦e₁⟧ ⟦e₂⟧) ⟦e₀⟧) M σ ρ Γ 𝒳)

  ; Execute scrutiny
  (define-values (σ₀ δσ₀ Vs₀ Es₀ ℐs₀)
    (apply/values (acc-σ-ℰ σ (λ (ℰ) (-ℰ.if ℰ ⟦e₁⟧ ⟦e₂⟧))) (⟦e₀⟧ M σ ρ Γ 𝒳)))

  ; Run each branch
  (define-values (δσ* As* ℐs*)
    (for*/ans ([A₀ Vs₀])
      (match-define (-A Γ₀ (-W Vs₀ s₀)) A₀)
      (with-guarded-arity 1 ('TODO Γ₀ Vs₀) (V₀)
        (define-values (Γ₁ Γ₂) (MσΓ+/-Vs M σ₀ Γ₀ V₀ s₀))
        (⊔/ans (with-Γ Γ₁ (⟦e₁⟧ M σ₀ ρ Γ₁ 𝒳))
               (with-Γ Γ₂ (⟦e₂⟧ M σ₀ ρ Γ₂ 𝒳))))))

  (values (⊔/m δσ₀ δσ*) (∪ Es₀ As*) (∪ ℐs₀ ℐs*)))

(: ⟦-ℰ.@⟧ : (Listof -W¹) (Listof -⟦e⟧) -src-loc → -⟦ℰ⟧)
(define (((⟦-ℰ.@⟧ Ws ⟦e⟧s loc) ⟦e⟧) M σ ρ Γ 𝒳)
  (define-values (σ* δσ Vs Es ℐs)
    (apply/values (acc-σ-ℰ σ (λ (ℰ) (-ℰ.@ Ws ℰ ⟦e⟧s loc))) (⟦e⟧ M σ ρ Γ 𝒳)))

  (define l (-src-loc-party loc))

  (define-values (δσ* As* ℐs*)
    (match ⟦e⟧s
      [(cons ⟦e⟧* ⟦e⟧s*)
       (for*/ans ([A Vs])
         (match-define (-A Γ₀ (-W Vs₀ s₀)) A)
         (with-guarded-arity 1 (l Γ₀ Vs₀) (V₀)
           (define W (-W¹ V₀ s₀))
           (((⟦-ℰ.@⟧ (cons W Ws) ⟦e⟧s* loc) ⟦e⟧*) M σ* ρ Γ₀ 𝒳)))]
      ['()
       (for*/ans ([A Vs])
         (match-define (-A Γ₀ (-W Vs₀ s₀)) A)
         (with-guarded-arity 1 (l Γ₀ Vs₀) (V₀)
           (define W (-W¹ V₀ s₀))
           (match-define (cons W-f W-xs) (reverse (cons W Ws)))
           (ap M σ* Γ₀ 𝒳 W-f W-xs loc)))]))

  (values (⊔/m δσ δσ*) (∪ Es As*) (∪ ℐs ℐs*)))

(: ap : -M -σ -Γ -𝒳 -W¹ (Listof -W¹) -src-loc → (Values -Δσ (℘ -A) (℘ -ℐ)))
(define (ap M σ Γ 𝒳 W-f W-xs loc)
  (match-define (-W¹ V-f s-f) W-f)
  (define-values (V-xs s-xs)
    (for/lists ([V-xs : (Listof -V)] [s-xs : (Listof -s)])
               ([W-x W-xs])
      (match-define (-W¹ V s) W-xs)
      (values V s)))

  ;; TODO: guard against wrong arity
  
  (match V-f
    [(-Clo xs ⟦e*⟧ ρ)
     (define-values (δσ ρ*)
       (match xs
         [(? list? xs)
          (for/fold ([δσ : -Δσ ⊥σ] [ρ* : -ρ ρ])
                    ([x xs] [V V-xs])
            (define α (-α.x x Γ))
            (values (⊔ δσ α V) (ρ+ ρ* x α)))]
         [_ (error 'ap "TODO: varargs")]))
     (define 𝒳* (for/hash : -𝒳 ([x xs] [s s-xs] #:when s) (values x s)))
     (values δσ ∅ {set (-ℐ (-ℋ Γ 𝒳 s-f 𝒳* '□) (-ℬ ⟦e*⟧ ρ*))})]
    [(? symbol? o)
     (define-values (δσ As) (δ M σ Γ o W-xs loc))
     (values δσ As ∅)]
    [(-Ar (-=>i doms rst rng) (cons α s-g) l³)
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
    [_ (values ⊥σ {set (-A Γ (-blm (-src-loc-party loc) 'Λ 'procedure? (list V-f)))} ∅)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Proof Relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(:* σ-V-maybe-true? σ-V-maybe-false? : -σ -V → Boolean)
(define (σ-V-maybe-true? σ V)
  ;; TODO
  #t)
(define (σ-V-maybe-false? σ V)
  ;; TODO
  #t)

(: Γ+/-s : -Γ -s → (Values (Option -Γ) (Option -Γ)))
(define (Γ+/-s Γ s)
  ;; TODO
  (if s
      (values (Γ+ Γ s) (Γ+ Γ (-@ 'not (list s) -Λ)))
      (values Γ Γ)))

(: MσΓ+/-Vs : -M -σ -Γ -V -s → (Values (Option -Γ) (Option -Γ)))
(define (MσΓ+/-Vs M σ Γ V s)
  (define-values (Γ₁ Γ₂) (Γ+/-s Γ s))
  (values (and Γ₁ (σ-V-maybe-true? σ V) Γ₁)
          (and Γ₂ (σ-V-maybe-false? σ V) Γ₂)))

(: acc-σ-ℰ : -σ (-ℰ → -ℰ) → -Δσ (℘ -A) (℘ -ℐ) → (Values -σ -Δσ (℘ -A) (℘ -A) (℘ -ℐ)))
;; Accumulate result into initial store and context transformer
(define ((acc-σ-ℰ σ f) δσ As ℐs)
  (define-values (Vs Es) (set-partition (match-λ? (-A _ (? -W?))) As))
  (define ℐs*
    (for/set: : (℘ -ℐ) ([ℐ ℐs])
      (match-define (-ℐ (-ℋ Γ 𝒳 s 𝒳* ℰ) ℬ) ℐ)
      (-ℐ (-ℋ Γ 𝒳 s 𝒳* (f ℰ)) ℬ)))
  (define σ* (⊔/m σ δσ))
  (values σ* δσ Vs Es ℐs*))

(define-syntax-rule (with-guarded-arity n (l Γ Vs) (V) e ...)
  (match Vs
    [(list V)
     e ...]
    [_
     (define C #|HACK|# (string->symbol (format "~a value(s)" n)))
     (values ⊥σ {set (-A Γ (-blm l 'Λ C (list (-b (length Vs)))))} ∅)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: δ : -M -σ -Γ Symbol (Listof -W¹) -src-loc → (Values -Δσ (Setof -A)))
(define (δ M σ Γ o Ws loc)
  (error "TODO"))
