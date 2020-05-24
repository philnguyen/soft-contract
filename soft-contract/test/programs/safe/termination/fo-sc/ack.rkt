#lang racket/base

(require soft-contract/fake-contract)

(define (a m n)
  (cond [(zero? m) (+ 1 n)]
        [(zero? n) (a (- m 1) 1)]
        [else (a (- m 1) (a m (- n 1)))]))

(provide
 (contract-out
  [a (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
