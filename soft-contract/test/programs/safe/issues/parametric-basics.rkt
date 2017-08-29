#lang racket

(define (id x) x)

(define (use-map map)
  (map (λ (x) (/ 1 x)) '(42 43 44)))

(define (use-compose compose)
  ((compose add1 add1) 42))

(provide
 (contract-out
  [id (parametric->/c (α) (α . -> . α))]
  [use-map
   ((parametric->/c (α β) ((α . -> . β) (listof α) . -> . (listof β)))
    . -> .
    (listof number?))]
  [use-compose
   ((parametric->/c (α β γ) ((β . -> . γ) (α . -> . β) . -> . (α . -> . γ)))
    . -> .
    exact-positive-integer?)]))
