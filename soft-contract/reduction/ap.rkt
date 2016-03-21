#lang typed/racket/base

(provide ap)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../delta.rkt")

(: ap : Mon-Party -ℓ -W¹ (Listof -W¹) → -⟦e⟧)
;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define ((ap l ℓ Wₕ Wₓs) M σ ℒ₀)
  (match-define (-ℒ ρ₀ Γ₀ 𝒞₀) ℒ₀)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ (apply -?@ sₕ sₓs))

  ;; TODO: guard against wrong arity

  (: ap/δ : Symbol → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
  ;; Apply primitive
  (define (ap/δ o)
    (define-values (δσ A*) (δ 𝒞₀ ℓ M σ Γ₀ o Wₓs))
    (cond [(list? A*)
           (values δσ {set (-ΓW Γ₀ (-W A* sₐ))} ∅ ∅)]
          ;; Rely on `δ` giving no error
          [else (⊥ans)]))

  (: ap/β : -formals -⟦e⟧ -ρ -Γ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ)))
  ;; Apply λ abstraction
  (define (ap/β xs ⟦e⟧ ρ Γ₁)
    (define 𝒞₁ (𝒞+ 𝒞₀ (cons ⟦e⟧ ℓ)))
    (define-values (δσ ρ₁)
      (match xs
        [(? list? xs)
         (for/fold ([δσ : -Δσ ⊥σ] [ρ : -ρ ρ])
                   ([x xs] [V Vₓs])
           (define α (-α.x x 𝒞₁))
           (values (⊔ δσ α V) (ρ+ ρ x α)))]
        [_ (error 'ap/β "TODO: varargs")]))
    (define bnds (map (inst cons Symbol -s) xs sₓs))
    (define ℬ₁ (-ℬ ⟦e⟧ (-ℒ ρ₁ Γ₁ 𝒞₁)))
    (values δσ ∅ ∅ {set (-ℐ (-ℋ ℒ₀ sₕ bnds '□) ℬ₁)}))
  
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
    [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅)]))
