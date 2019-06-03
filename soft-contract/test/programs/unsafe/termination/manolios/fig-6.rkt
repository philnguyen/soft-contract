#lang racket/base

(require soft-contract/fake-contract)

(define (g x) (f (+ x 1)))
(define (h x) (f #|HERE|#x))
(define (f x)
  (cond [(= x 0) 0]
        [(< x 0) (g x)]
        [else (h x)]))

(provide
 (contract-out
  [f (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
