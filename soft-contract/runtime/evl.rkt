#lang typed/racket/base

(provide evl@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         typed/racket/unit
         typed-racket-hacks
         "signatures.rkt")

(define-unit evl@
  (import)
  (export evl^)

  (: R↓ : (U V V^ A) Φ^ → R^)
  ;; TODO inefficient
  (define (R↓ x Φ^)
    (define A (cond [(set? x) (list x)]
                    [(A? x) x]
                    [else (list {set x})]))
    (for/set : R^ ([Φ (in-set Φ^)])
      (R A Φ))))
