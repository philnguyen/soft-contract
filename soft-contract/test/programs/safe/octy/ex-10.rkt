#lang racket
(require soft-contract/fake-contract)

(define (f p)
  (if (number? (car p)) (add1 (car p)) 7))

(provide/contract [f (cons? . -> . number?)])
