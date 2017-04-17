#lang racket

(provide/contract
 [main (integer? . -> . (and/c integer? (>=/c 0)))])

(define (g x) (λ (_) x))

(define (twice f x y) ((f (f x)) y))

(define (neg x) (λ (_) (- 0 (x #f))))

(define (main n)
  (if (>= n 0)
      (twice neg (g n) 'unit)
      42))
