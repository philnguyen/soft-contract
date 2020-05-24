#lang racket

(define s (set 1 2 3))
(define s1 (set-add s "bar"))
(define s2 (set))

(provide
 (contract-out
  [s1 (set/c integer?)]))
