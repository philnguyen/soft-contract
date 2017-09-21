#lang racket

(define (f x)
  (if (integer? x)
      (add1 x)
      x))

(provide
 (contract-out
  [f (parametric->/c (α) (α . -> . α))]))
