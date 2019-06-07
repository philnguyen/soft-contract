#lang racket

(define (main x xs) (list* x xs))

(provide
 (contract-out
  [main (integer? (listof string?) . -> . (listof integer?))]))
