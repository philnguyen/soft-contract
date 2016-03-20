; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/eta.sch
#lang racket
(require soft-contract/fake-contract)

(define (do-something)
  10)

(define (id y)
  (do-something)
  y)

((id (λ (a) a)) #t)
((id (λ (b) b)) #f)
