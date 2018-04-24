#lang racket

(provide/contract
 [main ((and/c integer? (>=/c 0)) . -> . (and/c integer? (>=/c 0)))])

(define (g x) (λ (_) x))

(define (twice f x y) ((f (f x)) y))

(define (neg x) (λ (_) (- 0 (x #f))))

(define (main n)
  (twice neg (g n) 'unit))
