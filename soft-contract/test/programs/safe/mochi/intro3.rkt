#lang racket

(define (f x g) (g (+ x 1)))
(define (main n h)
  (if (>= n 0) (f n (h n)) 'unit))

(provide
 (contract-out
  [main (integer?
         (->i ([z integer?]) (res (z) ((and/c integer? (>/c z)) . -> . any/c)))
         . -> . any/c)]))
