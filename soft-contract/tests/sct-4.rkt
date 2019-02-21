#lang racket/base

(require soft-contract/fake-contract)

(define (p m n r)
  (cond [(> r 0) (p m (- r 1) n)]
        [(> n 0) (p r (- n 1) m)]
        [else m]))

(provide
 (contract-out
  [p (exact-nonnegative-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
