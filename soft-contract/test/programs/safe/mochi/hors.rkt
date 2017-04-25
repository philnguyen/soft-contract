#lang racket

(define (c _) 'unit)
(define (b x _) (x 1))
(define (a x y q) (begin (x 0) (y 0)))
(define (f n x q)
  (if (<= n 0) (x q)
      (a x (λ (p) (f (- n 1) (λ (_) (b x _)) p)) q)))
(define (s n q) (f n c q))

(define (main n) (s n 0))

(provide/contract [main (integer? . -> . any/c)])
