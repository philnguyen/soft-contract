#lang typed/racket/base

(require
 racket/set
 "../utils/main.rkt"
 "../ast/definition.rkt"
 "../parse/main.rkt"
 "../runtime/main.rkt"
 "step.rkt" "init.rkt")

(: run-files : Path-String * → (℘ -A))
(define (run-files . ps)
  (run (files->modules ps)))

(: run : (Listof -module) → (℘ -A))
(define (run ms)
  
  (: loop : (HashTable -ℬ -σ) (℘ -ℬ) (℘ -Co) -M -Ξ -σ → (Values -M -Ξ -σ))
  (define (loop seen ℬs Cos M Ξ σ)
    (cond
      [(and (set-empty? ℬs) (set-empty? Cos))
       (values M Ξ σ)]
      [else
       ;; Widen global tables
       (define-values (δM δΞ δσ) (⊔³ (ev* M Ξ σ ℬs) (co* M Ξ σ Cos)))
       (define-values (M* Ξ* σ*) (⊔³ (values M Ξ σ) (values δM δΞ δσ)))
       ;; Check for un-explored configuation (≃ ⟨e, ρ, σ⟩)
       (define-values (ℬs* seen*)
         (for/fold ([ℬs* : (℘ -ℬ) ∅] [seen* : (HashTable -ℬ -σ) seen])
                   ([ℬ (in-hash-keys δΞ)] #:unless (equal? (hash-ref seen -ℬ #f) σ*))
           (values (set-add ℬs* ℬ) (hash-set seen* ℬ σ*))))
       (define Cos*
         (∪ (for*/set: : (℘ -Co) ([(ℬ As) (in-hash δM)] #:unless (set-empty? As)
                                  [ℛ (in-set (Ξ@ Ξ* ℬ))])
              (-Co ℛ As))
            (for*/set: : (℘ -Co) ([(ℬ ℛs) (in-hash δΞ)]
                                  [As (in-value (M@ M* ℬ))] #:unless (set-empty? As)
                                  [ℛ (in-set ℛs)])
              (-Co ℛ As))))
       (loop seen* ℬs* Cos* M* Ξ* σ*)]))

  (define-values (σ₀ e₀) (𝑰 ms))
  (define ℬ₀ (-ℬ (⇓ₚ ms e₀) ⊥ρ))
  (define-values (M Ξ σ) (loop (hash ℬ₀ σ₀) {set ℬ₀} ∅ ⊥M ⊥Ξ σ₀))
  (M@ M ℬ₀))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊔³ x y)
  (let-values ([(x₁ x₂ x₃) x]
               [(y₁ y₂ y₃) y])
    (values (⊔/m x₁ y₁) (⊔/m x₂ y₂) (⊔/m x₃ y₃))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
