#lang racket

(define (id1 x) 42)
(define (id2 x) x)

(provide
 (contract-out
  [id1 (parametric->/c (α) (α . -> . α))]
  [id2 (parametric->/c (α β) (α . -> . β))]))
