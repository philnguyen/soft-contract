#lang racket
(require soft-contract/fake-contract)

(define (id x) x)

(provide
 (contract-out
  [id (->i ([x any/c]) (res (x) (λ (a) (equal? a x))))]))
