#lang racket
(require soft-contract/fake-contract)

(define (f n)
  (/ 1 (- 100 n)))

(provide (contract-out [f (integer? . -> . integer?)]))
