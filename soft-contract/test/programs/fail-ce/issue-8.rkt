#lang racket
(require soft-contract/fake-contract)

(define (sqr n)
  (* n n))

(provide 
 (contract-out 
  [sqr (integer? . -> . (and/c integer? (lambda (x) (> x 0))))]))
