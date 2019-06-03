#lang racket/base

(require soft-contract/fake-contract)

(define (range lo hi)
  (cond [(< lo hi) (cons lo (range #|HERE|# lo hi))]
        [else '()]))

(provide
 (contract-out
  [range (exact-nonnegative-integer? exact-nonnegative-integer? . -> . list? #:total? #t)]))
