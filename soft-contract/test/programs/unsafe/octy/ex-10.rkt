#lang racket
(require soft-contract/fake-contract)

(define (f p)
  (if (number? (car p)) (add1 (car p)) #|HERE|# (add1 p)))

(provide/contract [f (cons? . -> . number?)])
