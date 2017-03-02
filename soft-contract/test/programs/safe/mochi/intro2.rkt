#lang racket

(define (f x g) (g (+ x 1)))
(define (main n h)
    (if (>= n 0) (f n h) 'unit))

(provide
 (contract-out
  [main (integer? ((and/c integer? (>/c 0)) . -> . any/c) . -> . any/c)]))
