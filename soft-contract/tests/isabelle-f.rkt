#lang racket/base

(require soft-contract/fake-contract)

(define (f n m)
  (cond [(zero? m) n]
        [(zero? n) (f m m)]
        [else (f (sub1 m) (sub1 n))]))

(provide
 (contract-out
  [f (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
