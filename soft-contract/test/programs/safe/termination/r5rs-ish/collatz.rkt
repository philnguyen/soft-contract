#lang racket/base

(require soft-contract/fake-contract)

;; This variant of the benchmark uses `/'.
;; See "collatz-q.sch" for the `quotient' variant.

(define (cycle-length n)
  (cond
   [(= n 1)
    1]
   [(odd? n)
    (+ 1 (cycle-length (+ 1 (* 3 n))))]
   [(even? n)
    (+ 1 (cycle-length (/ n 2)))]))

(provide
 (contract-out
  [cycle-length (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
