#lang racket

(define h1 (hash 1 2))
(define h2 (hash-set (hash-set h1 1 2) 'a 'b))

(provide
 (contract-out
  [h2 (hash/c integer? integer?)]))
