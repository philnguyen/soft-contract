#lang typed/racket/base

(provide run@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         racket/list
         typed/racket/unit
         set-extras
         typed-racket-hacks
         unreachable
         bnf
         traces/typed
         intern
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "compile.rkt"
         "step.rkt"
         "app.rkt"
         )

(define-unit run@
  (import env^ sto^ alloc^
          compile^ step^)
  (export run^)

  (: inj : (U -prog ⟦E⟧) → (Values Ξ Σ))
  (define (inj x)
    (define ⟦E⟧ (->⟦E⟧ x))
    (define αₖ₀ (αₖ ⟦E⟧ ⊥Ρ))
    (define Σ₀ (Σ ⊥Σᵥ ⊥Σₖ ⊥Σₐ))
    (values (⟦E⟧ ⊥Ρ {set ∅} (Ξ:co '() αₖ₀ H₀) Σ₀) Σ₀))

  (: run : (U -prog ⟦E⟧) → (Values (℘ Blm) Σ))
  (define (run p)
    (define-values (Ξ₀ Σ) (inj p))
    ;; TODO real versioning
    (Ver . ≜ . (List Σᵥ Σₖ Σₐ)) 
    (define seen : (Mutable-HashTable Ξ:co Ver) (make-hash))
    (define (ver) : Ver (list (Σ-val Σ) (Σ-kon Σ) (Σ-evl Σ)))
    (define-set blms : Blm)

    (let loop ([front : (℘ Ξ) {set Ξ₀}])
      (if (set-empty? front)
          (values blms Σ)
          (let ([front* 
                 (for*/set : (℘ Ξ) ([Ξ₀ (in-set front)]
                                    [Ξ₁ (in-set (↝! Ξ₀ Σ))]
                                    #:unless (and (Blm? Ξ₁) (blms-add! Ξ₁))
                                    [v₁ (in-value (ver))]
                                    #:unless (equal? v₁ (hash-ref seen Ξ₁ #f)))
                   (hash-set! seen Ξ₁ v₁)
                   Ξ₁)])
            (loop front*)))))

  (: viz : (U -prog ⟦E⟧) → Σ)
  (define (viz p)
    ;; Compacting each store to its version to display
    (Ξ* . ≜ . (List Ξ Iᵥ Iₖ Iₐ))
    
    (define-values (Ξ₀ Σ₀) (inj p))

    (define (Ξ->Ξ* [Ξ : Ξ]) : Ξ*
      ;; depending on mutable state Σ₀
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (list Ξ (Iᵥ-of Σᵥ) (Iₖ-of Σₖ) (Iₐ-of Σₐ)))
    
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (match-lambda
        [(list Ξ _ _ _) (map/set Ξ->Ξ* (↝! Ξ Σ₀))]))
    (function-traces ↝₁ (Ξ->Ξ* Ξ₀))
    Σ₀)

  (: ->⟦E⟧ : (U -prog ⟦E⟧) → ⟦E⟧)
  (define (->⟦E⟧ x) (if (-prog? x) (↓ₚ x) x))
  )

(define-interner Iᵥ Σᵥ)
(define-interner Iₖ Σₖ)
(define-interner Iₐ Σₐ)
