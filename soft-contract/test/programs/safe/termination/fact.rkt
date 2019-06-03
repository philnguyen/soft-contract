#lang racket

(require soft-contract/fake-contract)

(define (fact n)
  (if (<= n 0) 1 (* n (fact (sub1 n)))))

(provide
 (contract-out
  [fact (exact-integer? . -> . exact-positive-integer? #:total? #t)]))
