#lang racket
(require soft-contract/fake-contract)

(define (f x y)
  (cond
   [(and (number? x) (string? y)) (and (number? x) (string? y))]
   [(number? x) (and (number? x) (not (string? y)))]
   [else (not (number? x))]))

(provide/contract [f (any/c any/c . -> . (not/c false?))])
