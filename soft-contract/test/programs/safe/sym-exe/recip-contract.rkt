#lang racket
(require soft-contract/fake-contract)

(define (recip x) (/ 1 x))

(define non-zero/c (and/c real? (not/c zero?)))

(provide/contract [recip (non-zero/c . -> . non-zero/c)]
		  [non-zero/c any/c])
