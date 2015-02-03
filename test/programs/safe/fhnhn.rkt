#lang racket
(require soft-contract/fake-contract)

(define (h x) (λ (_) x))

(define (g n) ((f (h n)) (h n)))

(define (main m) (g m))

(provide/contract
 [f (->i ([x (any/c . -> . integer?)])
	 (res (x)
	      ((and/c (any/c . -> . integer?)
		      (λ (y) (not (and (> (x #f) 0) (< (y #f) 0))))) . -> . integer?)))]
 [main (integer? . -> . integer?)]
 [h (integer? . -> . (any/c . -> . integer?))]
 [g (integer? . -> . integer?)])
