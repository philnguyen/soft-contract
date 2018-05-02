#lang typed/racket/base

(provide evl@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         racket/splicing
         typed/racket/unit
         typed-racket-hacks
         set-extras
         unreachable
         "signatures.rkt")

(define-unit evl@
  (import val^)
  (export evl^)

  (define ⊤Φ (Φ (hasheq) (hash)))
  (define ⊥Φ^ {set ⊤Φ})

  (: Φ@ : Φ (Listof T) → (℘ P))
  (define (Φ@ Φ Ts) (hash-ref (Φ-condition Φ) Ts mk-∅))

  (: T->R : (U T T^) Φ^ → R)
  (define (T->R x Φ^)
    (R (if (set? x) (list x) (list (set x))) Φ^))

  (: filter/arity : R^ Natural → (Values R^ W^))
  (define (filter/arity R^ n)
    (define-set others : W)
    (define-set R^-filtered : R)
    (for ([R* (in-set R^)])
      (match-define (R W* _) R*)
      (if (= n (length W*))
          (R^-filtered-add! R*)
          (others-add! W*)))
    (values R^-filtered others))

  (: collapse-R^ : R^ → (Values W^ Φ^))
  (define (collapse-R^ R^)
    (for/fold ([W^ : W^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R W* Φ^*) R*)
      (values (set-add W^ W*) (∪ Φ^ Φ^*)))) 

  (: collapse-R^-1 : R^ → (Values T^ Φ^))
  (define (collapse-R^-1 R^)
    (for/fold ([T^ : T^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R (list T^*) Φ^*) R*)
      (values (T⊔ T^ T^*) (∪ Φ^ Φ^*))))

  (: collapse-R^/Φ^ : R^ → Φ^)
  (define (collapse-R^/Φ^ R^) (set-union-map R-_1 R^))

  (: collapse-R^/W^ : R^ → W^)
  (define (collapse-R^/W^ R^) (map/set R-_0 R^))

  (define R⊔ : (R R → R)
    (match-lambda**
     [((R W₁ Φ^₁) (R W₂ Φ^₂)) (R (map T⊔ W₁ W₂) (∪ Φ^₁ Φ^₂))]))

  (define R⊔₁ : (R (Listof T) Φ → R)
    (match-lambda**
     [((R W Φ^) Ts Φ) (R (map T⊔₁ W Ts) (set-add Φ^ Φ))]))

  (: validate-R : ?R → ?R)
  (define (validate-R R)
    (and R
         (not (set-empty? (R-_1 R)))
         (not (ormap (inst set-empty? T) (R-_0 R)))
         R))

  (: with-2-paths (∀ (X) (→ (Values R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X)))
  (define (with-2-paths mk on-t on-f)
    (define-values (R^₁ R^₂) (mk))
    (∪ (if (set-empty? R^₁) ∅ (on-t R^₁))
       (if (set-empty? R^₂) ∅ (on-f R^₂))))

  (: with-3-paths (∀ (X) (→ (Values R^ R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X)))
  (define (with-3-paths mk f₁ f₂ f₃)
    (define-values (R^₁ R^₂ R^₃) (mk))
    (∪ (if (set-empty? R^₁) ∅ (f₁ R^₁))
       (if (set-empty? R^₂) ∅ (f₂ R^₂))
       (if (set-empty? R^₃) ∅ (f₃ R^₃))))

  (splicing-local
      ((: with-collapse (∀ (X) (Φ^ → (℘ X)) → R^ → (℘ X)))
       (define ((with-collapse on-Φ^) R^) (on-Φ^ (collapse-R^/Φ^ R^))))
    (: with-2-paths/collapse : (∀ (X) (→ (Values R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
    (define (with-2-paths/collapse mk on-t on-f)
      (with-2-paths mk (with-collapse on-t) (with-collapse on-f)))
    (: with-3-paths/collapse : (∀ (X) (→ (Values R^ R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
    (define (with-3-paths/collapse mk f₁ f₂ f₃)
      (with-3-paths mk (with-collapse f₁) (with-collapse f₂) (with-collapse f₃))))
  
  )
