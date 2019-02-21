#lang racket/base

(require soft-contract/fake-contract)

(define (f x)
  (cond [(<= x 1) 0]
        [(= 1 (modulo x 2)) (f (+ x 1))]
        [else (+ 1 (f (quotient x 2)))]))

(provide
 (contract-out
  [f (integer? . -> . integer? #:total? #t)]))
