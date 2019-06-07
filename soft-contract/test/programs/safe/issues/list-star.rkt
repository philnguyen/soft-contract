#lang racket

(define (main x xs) (list* x xs))

(provide
 (contract-out
  [main (integer? (listof integer?) . -> . (listof integer?))]))
