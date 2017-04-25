#lang racket

(define h1 (hash))
(define h2 (hasheq 'foo 1))
(define h3 (hasheqv 'foo 1 'bar 2 'qux 3))

(provide
 (contract-out
  [h1 hash?]
  [h2 (not/c integer?)]
  [h3 (and/c hash? immutable?)]))
