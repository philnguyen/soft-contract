#lang racket
(require soft-contract/fake-contract)

(define (foldr1 f xs)
  (let ([z (car xs)]
	[zs (cdr xs)])
    (if (empty? zs) z
	(f z (foldr1 f zs)))))

(provide/contract [foldr1 ((any/c any/c . -> . any/c) (nelistof any/c) . -> . any/c)])
