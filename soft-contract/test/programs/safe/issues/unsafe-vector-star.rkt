#lang racket/base

(require racket/contract
         racket/unsafe/ops)

(define v (vector 1 2 3))
(define n (unsafe-vector*-ref v 0))
(define l (unsafe-vector*-length v))

(define (f xs) xs)

(provide
 (contract-out
  [n integer?]
  [l fixnum?]
  [f ((vectorof integer?) . -> . impersonator?)]))
