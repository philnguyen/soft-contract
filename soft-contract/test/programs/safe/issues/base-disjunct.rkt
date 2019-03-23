#lang racket

(define c (or/c #f #t))
(define u #f)
(define v #t)

(provide
 (contract-out [u c]
               [v c]))
