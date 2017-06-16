#lang racket

(provide
  (contract-out
    (foo? (-> any/c boolean?))
    (make-foo (-> exact-nonnegative-integer? foo?))))

(struct foo (val))

(define (make-foo n)
  (foo n))
