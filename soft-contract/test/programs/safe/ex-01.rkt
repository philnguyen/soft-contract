#lang racket
(require soft-contract/fake-contract)

(define (f x)
  (if (number? x) (add1 x) 0))

(provide/contract [f (any/c . -> . number?)])
