#lang racket
(require soft-contract/fake-contract)

(define (f x y)
  (if (if (number? x) (string? y) #f)
      (+ x (string-length y))
      0))

(provide/contract [f (any/c any/c . -> . number?)])
