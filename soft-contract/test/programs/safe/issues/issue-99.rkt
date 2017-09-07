#lang racket/base
(require racket/contract)
(provide (contract-out (f (-> (or/c (one-of/c #f) integer?) zero?))))

(define (f x)
  0)
