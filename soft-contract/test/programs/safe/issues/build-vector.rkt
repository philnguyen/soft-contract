#lang racket

(provide
 (contract-out
  [v1 (vectorof integer?)]
  [v2 (vectorof string?)]))

(define v1
  (build-vector 42 values))

(define v2
  (build-vector 0 number->string))
