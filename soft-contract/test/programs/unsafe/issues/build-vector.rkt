#lang racket

(provide
 (contract-out
  [v (vectorof integer?)]))

(define v
  (build-vector 3 number->string))
