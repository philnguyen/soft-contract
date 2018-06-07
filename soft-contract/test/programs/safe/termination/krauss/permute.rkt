#lang racket/base

(require soft-contract/fake-contract)

(define (p m n r)
  (cond [(< 0 r) (p m (- r 1) n)]
        [(< 0 n) (p r (- n 1) m)]
        [else m]))

(provide
 (contract-out
  [p (exact-nonnegative-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
