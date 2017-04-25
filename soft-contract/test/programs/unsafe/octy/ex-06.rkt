#lang racket
(require soft-contract/fake-contract)

(define (f x y)
  (if (and (number? x) (string? y))
      (+ x (string-length y))
      (string-length x)))

(provide/contract [f (#|HERE|# any/c string? . -> . number?)])
