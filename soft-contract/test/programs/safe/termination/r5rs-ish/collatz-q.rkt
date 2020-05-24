#lang racket/base

(require soft-contract/fake-contract)

(define (cycle-length n)
  (cond
   [(= n 1)
    1]
   [(odd? n)
    (+ 1 (cycle-length (+ 1 (* 3 n))))]
   [(even? n)
    (+ 1 (cycle-length (quotient n 2)))]))

(provide
 (contract-out
  [cycle-length (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
