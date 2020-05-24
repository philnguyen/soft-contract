#lang racket

(define t (make-thread-cell 42))
(thread-cell-set! t "43")
(define v (thread-cell-ref t))

(provide
 (contract-out
  [v exact-nonnegative-integer?]))
