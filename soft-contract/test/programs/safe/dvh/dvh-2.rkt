#lang racket
(require soft-contract/fake-contract)

(define (main x) (lambda (y) y))

(provide/contract
 [main (->i ([x number?])
	    (res (x) (->i ([y (and/c number? (=/c x))])
			  (res (y) (=/c x)))))])
