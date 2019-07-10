#lang racket

(define c1 "♥")
(define c2 "♦")
(define c3 "♣")
(define c4 "♠")
(define c (or/c c1 c2 c3 c4))

(define (f x) x)

(provide
 (contract-out
  [f ((or/c c "■") . -> . c)]))
