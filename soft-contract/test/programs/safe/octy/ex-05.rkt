#lang racket

(define (f x y)
  (if (and (number? x) (string? y)) (+ x (string-length y)) 0))

(provide/contract [f (any/c any/c . -> . number?)])
