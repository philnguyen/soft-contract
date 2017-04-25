#lang racket

(require soft-contract/fake-contract)

(define (foo s)
  (/ (string-length s) 2))

(provide
 (contract-out [foo (string? . -> . (or/c string? integer?))]))
