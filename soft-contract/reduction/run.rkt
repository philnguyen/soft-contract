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
    (values (⟦E⟧ ⊥Ρ {set ∅} (K '() αₖ₀) H₀ Σ₀) Σ₀))

  (: run : (U -prog ⟦E⟧) → (Values (℘ Blm) Σ))
  (define (run p)
    (define-values (Ξ₀ Σ) (inj p))
    ;; TODO real versioning
    (Ver . ≜ . (List Σᵥ Σₖ Σₐ))
    (define seen : (Mutable-HashTable Ξ Ver) (make-hash))
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
    ;; Versioning
    (Ξ* . ≜ . (List Ξ Index Index Index)) 
    (define-values (Σᵥ->v v->Σᵥ) ((inst mk-versioning Σᵥ)))
    (define-values (Σₖ->v v->Σₖ) ((inst mk-versioning Σₖ)))
    (define-values (Σₐ->v v->Σₐ) ((inst mk-versioning Σₐ)))
    (define (Σ->v [Σ₀ : Σ])
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (values (Σᵥ->v Σᵥ) (Σₖ->v Σₖ) (Σₐ->v Σₐ)))
    ;; Wrapping
    (define-values (Ξ₀ Σ₀) (inj p))
    (define Ξ₀* : Ξ*
      (let-values ([(v₀ k₀ a₀) (Σ->v Σ₀)])
        (list Ξ₀ v₀ k₀ a₀)))
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (match-lambda
        [(list Ξ _ _ _)
         (for/set : (℘ Ξ*) ([Ξ₁ (in-set (↝! Ξ Σ₀))])
           (define-values (v k a) (Σ->v Σ₀))
           (list Ξ₁ v k a))]))
    (function-traces ↝₁ Ξ₀*)
    Σ₀)

  (: ->⟦E⟧ : (U -prog ⟦E⟧) → ⟦E⟧)
  (define (->⟦E⟧ x) (if (-prog? x) (↓ₚ x) x))

  (: mk-versioning (∀ (X) → (Values (X → Index) (Index → X))))
  (define (mk-versioning)
    (define x->i : (Mutable-HashTable X Index) (make-hash))
    (define i->x : (Mutable-HashTable Index X) (make-hasheq))
    (values
     (λ (x)
       (hash-ref! x->i x (λ ()
                           (define i (hash-count x->i))
                           (hash-set! i->x i x)
                           i)))
     (λ (i) (hash-ref i->x i))))
  )
