#lang racket

(define same? (equal? (make-vector 3 1) (make-vector 3)))

(provide
 (contract-out
  [same? values]))
