#lang racket/base

(require racket/match
         soft-contract/fake-contract)

(define (length l)
  (if (pair? l)
      (+ 1 (length (cdr l)))
      0))

(provide
 (contract-out
  [length ((listof any/c) . -> . integer? #:total? #t)]))
