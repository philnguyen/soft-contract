#lang racket/base

(define (f x)
  (define a (+ x 1))
  (define b (/ 1 x))
  0)

(require racket/contract)
(provide
  (contract-out (f (-> any/c real?))))
