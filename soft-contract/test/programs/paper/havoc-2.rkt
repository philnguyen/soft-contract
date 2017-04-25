#lang racket

(provide/contract
 [main ((any/c . -> . (-> any/c)) . -> . any/c)])

(define (main f●)
  (define n -3)
  (define (inc!) (set! n (add1 n)))
  (define (app) (/ 1 n))
  (define h (f● app))
  (f● inc!)
  (h))
