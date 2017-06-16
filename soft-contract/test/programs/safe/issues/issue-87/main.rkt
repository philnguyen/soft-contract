#lang racket
(require "foo.rkt")

(define (build-random-foo n)
  (make-foo 2))

(require racket/contract)
(provide (contract-out
  (build-random-foo (-> exact-nonnegative-integer? foo?))))
