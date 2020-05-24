#lang racket/base

(require soft-contract/fake-contract)

(define (tfact x n)
  (cond [(zero? n) x]
        [else (tfact (* n x) (- n 1))]))

(provide
 (contract-out
  [tfact (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
