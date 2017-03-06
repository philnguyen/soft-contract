#lang racket
(require soft-contract/fake-contract)

(define (taut b)
  (cond
   [(boolean? b) b]
   [else (and (taut (b #t)) (taut (b #f)))]))

(define prop/c
  ((or/c boolean? #|HERE|# procedure?) . -> . boolean?))

(provide/contract
 [taut prop/c]
 [prop/c any/c])
