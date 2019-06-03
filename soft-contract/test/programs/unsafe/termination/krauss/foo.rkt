#lang racket/base

(require soft-contract/fake-contract)

(define (foo flag? n m)
  (cond [(and flag? (> n 0)) (foo #t (sub1 n) (add1 m))]
        [(and flag? (zero? n)) (foo #f 0 m)]
        [(and (not flag?) (> m 0)) (foo #f (add1 n) #|HERE|# m)]
        [else n]))

(provide
 (contract-out
  [foo (boolean? exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
