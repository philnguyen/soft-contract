#lang racket

(define v 42)

(provide
 (contract-out [v (or/c #f #t)]))
