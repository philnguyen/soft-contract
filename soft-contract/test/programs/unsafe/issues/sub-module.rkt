#lang racket

(module sub racket
  (provide (contract-out [f (-> boolean? boolean?)]))
  (define (f y) y))

(module sub2 racket
  (require (submod ".." sub))
  (((lambda (x) x) f)
   ((lambda (z) z) 42)))
