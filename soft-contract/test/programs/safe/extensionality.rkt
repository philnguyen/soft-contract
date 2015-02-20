;; 1421365820240
#lang racket
(require soft-contract/fake-contract)

(define (f g)
  (= (g 5) (g 5)))

(provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
