#lang racket
(require soft-contract/fake-contract)

(define (h x) (λ (_) x))

(define (g f n) ((f (h n)) (h n)))

(define (main f m) (g f m))

(provide/contract
 [main ((->i ([x (any/c . -> . integer?)])
	 (res (x)
	      ((and/c (any/c . -> . integer?)
		      (λ (y) (not (and (> (x #f) 0) (< (y #f) 0))))) . -> . integer?)))
        integer? . -> . integer?)]
 [h (integer? . -> . (any/c . -> . integer?))])
