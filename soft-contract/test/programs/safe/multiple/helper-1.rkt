#lang racket

(require soft-contract/fake-contract)

(define (number=>string x) (number->string x))

(provide
 (contract-out
  [number=>string (number? . -> . string?)]))
