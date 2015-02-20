#lang racket
(require soft-contract/fake-contract)

(define (f g x)
  (if (>= x 0) (g x) (f (λ (x) (f g x)) (g x))))

(define (main n)
  (f add1 n))

(provide/contract [f ((integer? . -> . integer?) integer? . -> . integer?)]
		  [main (integer? . -> . (and/c integer? (>=/c 0)))])
