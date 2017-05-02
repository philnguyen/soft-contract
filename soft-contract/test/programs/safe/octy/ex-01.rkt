#lang racket

(define (f x)
  (if (number? x) (add1 x) 0))

(provide/contract [f (any/c . -> . number?)])
