#lang racket
(require soft-contract/fake-contract)

(define (f x y)
  (if (and (number? x) (string? y)) (+ x (string-length y)) #|HERE|# (+ x y)))

(provide/contract [f (any/c any/c . -> . number?)])
