#lang typed/racket/base

(provide evl@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         typed/racket/unit
         typed-racket-hacks
         set-extras
         "signatures.rkt")

(define-unit evl@
  (import)
  (export evl^)

  (: V->R : (U V V^) Φ^ → R)
  (define (V->R x Φ^)
    (define W^ (if (set? x) (set (list x)) (set (list (set x)))))
    (R W^ Φ^))

  (: W->R : (U W W^) Φ^ → R)
  (define (W->R x Φ^)
    (define W^ (if (set? x) x (set x)))
    (R W^ Φ^))

  (: filter/arity : R^ Natural → (Values R^ W^))
  (define (filter/arity R^ n)
    (define-set others : W)
    (define-set R^-filtered : R)
    (for ([R* (in-set R^)])
      (match-define (R W^* Φ^*) R*)
      (define W^-filtered
        (for/fold ([W^-filtered : W^ W^*])
                  ([W (in-set W^*)] #:unless (= n (length W)))
          (others-add! W)
          (set-remove W^-filtered W)))
      (R^-filtered-add! (R W^-filtered Φ^*)))
    (values R^-filtered others))

  (: collapse-R^ : R^ → (Values W^ Φ^))
  (define (collapse-R^ R^)
    (for/fold ([W^ : W^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R W^* Φ^*) R*)
      (values (∪ W^ W^*) (∪ Φ^ Φ^*))))

  (: collapse-R^/Φ^ : R^ → Φ^)
  (define (collapse-R^/Φ^ R^)
    (for/union : Φ^ ([R (in-set R^)]) (R-_1 R)))

  (: with-plausible-paths (∀ (X) (→ (Values Φ^ Φ^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
  (define (with-plausible-paths mk on-t on-f)
    (define-values (Φ^₁ Φ^₂) (mk))
    (∪ (if (set-empty? Φ^₁) ∅ (on-t Φ^₁))
       (if (set-empty? Φ^₂) ∅ (on-f Φ^₂))))
  )
