#lang typed/racket/base

(require "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "compile/kontinuation.rkt"
         racket/set
         racket/match)

(: ↝* : -ς -σ -σₖ -M → (Values (℘ -A) -σ -σₖ -M))
(define (↝* ς₀ σ σₖ M)
  
  (define seen : (HashTable -ς (List -σ -σₖ -M)) (make-hash))
  (define-set ans : -A)

  (let loop! ([front : (℘ -ς) {set ς₀}]
              [σ     : -σ  #|FIXME|# ⊥σ]
              [σₖ    : -σₖ #|FIXME|# ⊥σₖ]
              [M     : -M  ⊥M])
    (cond
      [(set-empty? front)
       (values ans σ σₖ M)]
      [else
       (error "TODO")])))

(: ↝ : -ς -σ -σₖ -M → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
;; Perform one "quick-step" on configuration,
;; Producing set of next configurations and store-deltas
(define (↝ ς σ σₖ M)
  (match ς
    [(-ς↑ αₖ Γ 𝒞) (↝↑ αₖ Γ 𝒞 σ σₖ M)]
    [(-ς↓ αₖ Γ A) (↝↓ αₖ Γ A σ σₖ M)]))

(: ↝↑ : -αₖ -Γ -𝒞 -σ -σₖ -M → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
;; Quick-step on "push" state
(define (↝↑ αₖ Γ 𝒞 σ σₖ M)
  (match αₖ
    [(-ℬ ⟦e⟧ ρ)
     (⟦e⟧ ρ Γ 𝒞 σ M (rt αₖ))]
    [_ (error '↝↑ "~a" αₖ)]))

(: ↝↓ : -αₖ -Γ -A -σ -σₖ -M → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
;; Quick-step on "pop" state
(define (↝↓ αₖ Γₑₑ A σ σₖ M)
  (for*/ans ([κ (σₖ@ σₖ αₖ)])
    (match-define (-κ ⟦k⟧ Γₑᵣ 𝒞ₑᵣ bnd) κ)
    ;; TODO:
    ;; - eliminate conflicting path-conditions
    ;; - strengthen Γₑᵣ with path-condition address if it's plausible
    (define Γₑᵣ* Γₑᵣ)
    (match A
      [(-W Vs s)
       (define sₐ (and s (binding->s bnd)))
       (⟦k⟧ (-W Vs sₐ) Γₑᵣ* 𝒞ₑᵣ σ M)]
      [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
       (⟦k⟧ blm Γₑᵣ* 𝒞ₑᵣ σ M)])))
