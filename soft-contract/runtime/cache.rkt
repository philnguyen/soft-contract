#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         set-extras
         unreachable
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(require typed/racket/unsafe)
(unsafe-require/typed racket/hash
  [hash-union (∀ (α β) ([(Immutable-HashTable α β)]
                        [#:combine (β β → β)]
                        #:rest (Immutable-HashTable α β)
                        . ->* .
                        (Immutable-HashTable α β)))])

(define-unit cache@
  (import sto^)
  (export cache^)

  (define ⊥A : (Pairof R (℘ Err)) (cons ⊥R ∅))

  (: R-of ([(U V V^ W)] [ΔΣ] . ->* . R))
  (define (R-of V [ΔΣ ⊥ΔΣ])
    (define (with [A : W]) (hash A {set ΔΣ}))
    (cond [(list? V) (with V)]
          [(set? V) (if (set-empty? V) ⊥R (with (list V)))]
          [else (with (list {set V}))]))

  (: ΔΣ⧺R : ΔΣ R → R)
  (define (ΔΣ⧺R ΔΣ R)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ ΔΣ₀)) R)]))

  (: R⧺ΔΣ : R ΔΣ → R)
  (define (R⧺ΔΣ R ΔΣ)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ₀ ΔΣ)) R)])) 

  (: collapse-R/ΔΣ : R → (Option ΔΣ))
  (define (collapse-R/ΔΣ R)
    (match (hash-values R)
      ['() #f]
      [(cons ΔΣs₀ ΔΣs*) (foldl ΔΣ⊔ (collapse-ΔΣs ΔΣs₀) (map collapse-ΔΣs ΔΣs*))]))

  (: collapse-R : R → (Option (Pairof W^ ΔΣ)))
  (define (collapse-R R)
    (and (not (hash-empty? R))
         (let*-values ([(W₀ ΔΣs₀ R*) (hash-first/rest R)]
                       [(Ws ΔΣ)
                        (for/fold ([Ws : W^ {set W₀}] [ΔΣ* : ΔΣ (collapse-ΔΣs ΔΣs₀)])
                                  ([(W ΔΣs) (in-hash R*)])
                          (values (set-add Ws W) (ΔΣ⊔ ΔΣ* (collapse-ΔΣs ΔΣs))))])
           (cons Ws ΔΣ))))

  (: R⊔ : R R → R)
  (define (R⊔ R₁ R₂)
    ((inst hash-union W (℘ ΔΣ)) R₁ R₂ #:combine set-union))

  (: map-R:ΔΣ : (ΔΣ → ΔΣ) R → R)
  (define (map-R:ΔΣ f R₀)
    (for/hash : R ([(W ΔΣs) (in-hash R₀)])
      (values W (map/set f ΔΣs))))
)
