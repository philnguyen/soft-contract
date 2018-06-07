#lang racket/base

(require soft-contract/fake-contract)

(define (f x)
  (cond [(or (not (integer? x)) (= x 0)) 0]
        [(< x 0) (f (+ x 1))]
        [else (f (- x 1))]))
(define (dec n)
  (cond [(or (not (integer? n)) (<= n 0)) 255]
        [else (- n 1)]))
(define (foo i j)
  (if (= i 1)
      (if (= j 1) 0 (foo (dec j) (dec j)))
      (foo (dec i) j)))

(provide
 (contract-out
  [f (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]
  [foo (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
