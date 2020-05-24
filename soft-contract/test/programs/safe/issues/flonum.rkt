#lang racket/base
(require racket/contract)

(define x 0.05)
(define (f x) x)

(provide
 (contract-out
  [x flonum?]
  [f (flonum? . -> . (and/c real? inexact?))]))
