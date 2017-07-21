#lang racket

(define same? (equal? (vector-length (make-vector 3 0)) (vector-length (make-vector 3))))

(provide
 (contract-out
  [same? values]))
