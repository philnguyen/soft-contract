#lang racket
(require soft-contract/fake-contract)

(define (foo s)
  (* s 3))

(provide (contract-out [foo (real? . -> . (not/c (=/c 1)))]))
