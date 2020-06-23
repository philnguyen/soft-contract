#lang racket/base

(require racket/contract)

(define n/c (parameter/c char?))
(define f/c (parameter/c (string? . -> . real?)))

(define (f param)
  (parameterize ([param (char-upcase (param))])
    (make-parameter 45)))

(define (g param)
  (parameterize ([param (λ (s) (+ 1 ((param) s)))])
    param))

(provide
 (contract-out
  [f (n/c . -> . n/c)]
  [g (f/c . -> . (parameter/c (string? . -> . integer?)))]))
