#lang racket/base

(require soft-contract/fake-contract)

(define ((g r) a) (r (r a)))
(define (f n) (if (zero? n) (λ (x) (+ 1 x)) (g (f #|HERE|# n))))

(provide
 (contract-out
  [f (exact-nonnegative-integer? . -> . (number? . -> . number?) #:total? #t)]))
