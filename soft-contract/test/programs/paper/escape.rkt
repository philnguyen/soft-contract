#lang racket

(provide/contract
 [f (((-> void?) . -> . void?) . -> . (and/c integer? (>=/c 0)))])

(define (f g)
  (define n 0)
  (define inc! (λ () (set! n (+ 1 n))))
  (g inc!)
  n)
