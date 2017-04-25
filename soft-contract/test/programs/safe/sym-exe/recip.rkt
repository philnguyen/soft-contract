#lang racket
(require soft-contract/fake-contract)

(define (recip x)
  (if (and (real? x) (not (zero? x)))
      (/ 1 x)
      "expect non-zero number"))

(provide/contract [recip (any/c . -> . (or/c (and/c real? (not/c zero?)) string?))])
