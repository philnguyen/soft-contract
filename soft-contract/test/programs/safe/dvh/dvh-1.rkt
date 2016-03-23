#lang racket
(require soft-contract/fake-contract)

(define (main x) (- (+ x x) x))

(provide/contract
 [main (->i ([z (and/c number? (=/c 5))])
	    (res (z) (=/c z)))])
