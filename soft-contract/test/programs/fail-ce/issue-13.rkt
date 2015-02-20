#lang racket
(require soft-contract/fake-contract)

(define (f g)
  (not (= (g 5) (g 7))))

(provide (contract-out [f ((integer? . -> . integer?) . -> . (lambda (x) x))]))
