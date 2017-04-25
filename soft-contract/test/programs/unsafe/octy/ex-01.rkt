#lang racket
(require soft-contract/fake-contract)

(define (f x)
  (if (number? x) (add1 x) #|HERE|# (add1 x)))

(provide/contract [f (any/c . -> . number?)])
