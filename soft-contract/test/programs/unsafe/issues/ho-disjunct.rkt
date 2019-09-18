#lang racket

(define c1 (cons/c 'x (integer? . -> . integer?)))
(define c2 (cons/c 'y (string? . -> . string?)))
(define c (or/c c1 c2))

(define f (list (cons 'x add1)
                (cons 'x string-append)))

(provide
 (contract-out
  [f (listof c)]))
