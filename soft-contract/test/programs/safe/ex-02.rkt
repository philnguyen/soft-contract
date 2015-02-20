#lang racket
(require soft-contract/fake-contract)

(define (f x)
  (if (number? x) (add1 x) (string-length x)))

(provide/contract [f ((or/c string? number?) . -> . number?)])
