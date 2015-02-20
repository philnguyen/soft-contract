#lang racket
(require soft-contract/fake-contract)

(define (f x) x)

(provide 
 (contract-out 
  [f (-> (lambda (x) (>= x 0)) any/c)]))
