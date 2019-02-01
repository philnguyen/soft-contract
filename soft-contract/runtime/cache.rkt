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

(define-unit cache@
  (import sto^)
  (export cache^)

  (define (⊥$) : $ (make-hash))
  (define ⊥A : (Pairof R (℘ Err)) (cons ⊥R ∅))

  (: R-of ([(U V V^ W)] [ΔΣ] . ->* . R))
  (define (R-of V [ΔΣ ⊥ΔΣ])
    (define (with [A : W^]) (hash ΔΣ A))
    (cond [(list? V) (with {set V})]
          [(set? V) (if (set-empty? V) ⊥R (with {set (list V)}))]
          [else (with {set (list {set V})})]))

  (: ΔΣ⧺R : ΔΣ R → R)
  (define (ΔΣ⧺R ΔΣ R)
    (if (hash-empty? ΔΣ) R (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ ΔΣ₀)) R)))

  (: R⧺ΔΣ : R ΔΣ → R)
  (define (R⧺ΔΣ R ΔΣ)
    (if (hash-empty? ΔΣ) R (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ₀ ΔΣ)) R))) 

  (: collapse-R/ΔΣ : R → (Option ΔΣ))
  (define (collapse-R/ΔΣ R)
    (match (hash-keys R)
      ['() #f]
      [(cons ΔΣ₀ ΔΣ*) (foldl ΔΣ⊔ ΔΣ₀ ΔΣ*)]))

  (: collapse-R : R → (Option (Pairof W^ ΔΣ)))
  (define (collapse-R R)
    (and (not (hash-empty? R))
         (let-values ([(ΔΣ Ws)
                       (for/fold ([ΔΣ* : ΔΣ ⊥ΔΣ] [Ws* : W^ ∅])
                                 ([(ΔΣ Ws) (in-hash R)])
                         (values (ΔΣ⊔ ΔΣ* ΔΣ) (∪ Ws* Ws)))])
           (cons Ws ΔΣ))))

  (: split-by-arity : W^ Natural → (Values W^ W^))
  (define (split-by-arity Ws n)
    ;; Favor common case where `Ws` is all ok, re-using old instance
    (for/fold ([ok : W^ Ws] [er : W^ ∅]) ([W (in-set Ws)])
      (if (= (length W) n)
          (values ok er)
          (values (set-remove ok W) (set-add er W)))))

  (: $⊔! : $ $:Key R (℘ Err) → Void)
  (define ($⊔! $ key r es)
    ((inst hash-update! $:Key (Pairof R (℘ Err)))
     $ key
     (match-lambda [(cons r₀ es₀) (cons (m⊔ r₀ r) (∪ es₀ es))])
     (λ () ⊥A)))

  (: map-R:ΔΣ : (ΔΣ → ΔΣ) R → R)
  (define (map-R:ΔΣ f R₀)
    (define R₁ (for/hash : R ([(ΔΣ Ws) (in-hash R₀)])
                 (values (f ΔΣ) Ws)))
    ;; Expect `f` to be injective
    (assert (= (hash-count R₀) (hash-count R₁)))
    R₁)
)
