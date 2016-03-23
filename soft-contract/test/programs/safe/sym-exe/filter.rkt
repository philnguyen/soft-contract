#lang racket
(require soft-contract/fake-contract)

(define (filter p? xs)
  (cond
   [(empty? xs) empty]
   [else (let ([x (car xs)]
	       [zs (filter p? (cdr xs))])
	   (if (p? x) (cons x zs) zs))]))

(provide/contract
 [filter ((any/c . -> . any/c) (listof any/c) . -> . (listof any/c))])
