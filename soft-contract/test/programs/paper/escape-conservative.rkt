#lang racket

(provide/contract
 [f (((-> void?) . -> . void?) . -> . (and/c (<=/c 2) integer?))])

(define (f g)
  (define n 0)
  (define inc! (λ () (set! n (+ 1 n))))
  (g inc!)
  (if (< n 2)
      (begin (g void) n)
      2))
