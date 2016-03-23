#lang racket
(require soft-contract/fake-contract)

(define (f x)
  (if (zero? x) 0
      (if (zero? (f (sub1 x))) 7 8)))

(provide/contract [f (integer? . -> . integer?)])
