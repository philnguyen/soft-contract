#lang racket

(define s (set 1 2 3))
(define s1 (set-add s "bar"))

(provide
 (contract-out
  [s (set/c integer?)]
  [s1 (set/c (or/c integer? string?))]))
