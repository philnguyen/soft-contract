#lang racket
(require soft-contract/fake-contract)

(define (f x)
  (if (= x 0) #f (cons x (g (- x 1)))))

(define (g x)
  (if (= x 0) #t (cons x (f (- x 1)))))

(provide/contract [f (integer? . -> . any/c)])
