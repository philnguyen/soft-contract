#lang racket
(require soft-contract/fake-contract)

(define (f x)
    (if (number? x) (add1 x) (string-length x)))

(define (g x)
  (if (let ([tmp (number? x)])
	(if tmp tmp (string? x)))
      (f x)
      0))

(provide/contract
 [f ((or/c string? number?) . -> . number?)]
 [g (any/c . -> . number?)])
