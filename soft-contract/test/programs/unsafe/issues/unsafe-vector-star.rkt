#lang racket/base

(require racket/contract
         racket/unsafe/ops)

(define v (vector 1 2 3))
(define n (unsafe-vector*-ref v 0))
(define l (unsafe-vector*-length v))

(define (f xs) (unsafe-vector*-ref xs 0))

(provide
 (contract-out
  [n integer?]
  [l fixnum?]
  [f ((vectorof integer?) . -> . integer?)]))
