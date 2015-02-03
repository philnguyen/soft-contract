#lang racket
(require soft-contract/fake-contract)

(define (taut b)
  (cond
   [(boolean? b) b]
   [else (and (taut (b #t)) (taut (b #f)))]))

(provide/contract
 [taut ([μ/c (X) (or/c boolean? [boolean? . -> . X])] . -> . boolean?)])
