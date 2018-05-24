#lang racket/base

(require soft-contract/fake-contract)

(define (fact n)
  (if (zero? n) 1 (* n (fact (sub1 n)))))

(provide/contract
 [fact (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)])
