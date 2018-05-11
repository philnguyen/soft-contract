#lang typed/racket/base

(provide approx@)

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         typed/racket/unit
         racket/splicing
         unreachable
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit approx@
  (import evl^
          prover^)
  (export approx^) 

  (: collapse-R^-1 : (U Σ Σᵥ) R^ → (Values T^ Φ^))
  (define (collapse-R^-1 Σ R^)
    (define ?retain (retainable-symbols (map/set R-_0 R^) 1))
    (match (?retain 0)
      [(? values S) (values S (set-union-map R-_1 R^))]
      [_ (for/fold ([T* : V^ ∅] [Φ^* : Φ^ ∅]) ([Rᵢ (in-set R^)])
           (match-define (R (list Tᵢ) Φ^ᵢ) Rᵢ)
           (values (∪ T* (T->V Σ Φ^ᵢ Tᵢ)) (∪ Φ^* Φ^ᵢ)))])) 

  (: collapse-value-lists : (U Σ Σᵥ) R^ Natural → R)
  (define (collapse-value-lists Σ Rs n)
    (define ?retain (retainable-symbols (map/set R-_0 Rs) n))
    (define W-vec : (Vectorof T^) (make-vector n ∅))
    (define-set Φs : Φ)
    (for ([Rᵢ (in-set Rs)])
      (match-define (R Wᵢ Φ^ᵢ) Rᵢ)
      (set! Φs (Φ^⊔ Φs Φ^ᵢ))
      (for ([Tₖ (in-list Wᵢ)] [k (in-range n)])
        (define Tₖ*
          (match (?retain k)
            [(? values S) S]
            [else (∪ (assert (vector-ref W-vec k) set?) (T->V Σ Φ^ᵢ Tₖ))]))
        (vector-set! W-vec k Tₖ*)))
    (R (vector->list W-vec) Φs))

  (: R⊔ : (U Σ Σᵥ) R R → R)
  (define (R⊔ Σ R₁ R₂)
    (match-define (R W₁ Φ^₁) R₁)
    (match-define (R W₂ Φ^₂) R₂)
    (define Φ^* (Φ^⊔ Φ^₁ Φ^₂))
    (R (W⊔ Σ Φ^* W₁ W₂) Φ^*))

  (: W⊔ : (U Σ Σᵥ) Φ^ W W → W)
  (define (W⊔ Σ Φ^ W₁ W₂)
    (for/list ([T₁ (in-list W₁)] [T₂ (in-list W₂)])
      (cond
        [(or (set? T₁) (set? T₂) (not (equal? T₁ T₂)))
         (∪ (T->V Σ Φ^ T₁) (T->V Σ Φ^ T₂))]
        [else T₁])))

  (: retainable-symbols ([W^] [Integer] . ->* . (Integer → (Option S))))
  (define (retainable-symbols Ws [n (apply max ((inst set-map W Index) Ws length))])
    (define vals : (Vectorof (Option S)) (make-vector n 'untouched))
    (for ([W (in-set Ws)])
      (for ([Tᵢ (in-list W)] [i (in-naturals)])
        (cond [(set? Tᵢ) (vector-set! vals i #f)]
              [else (match (vector-ref vals i)
                      ['untouched (vector-set! vals i Tᵢ)]
                      [(== Tᵢ) (void)]
                      [_ (vector-set! vals i #f)])])))
    (λ (i) (vector-ref vals i)))
  )
