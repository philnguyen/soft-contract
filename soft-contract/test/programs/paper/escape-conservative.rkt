#lang racket

(provide/contract
 [f ((any/c . -> . any) . -> . number?)])

(define (f g)
  (define n 0)
  (g (λ () (set! n 'nope)))
  n)
