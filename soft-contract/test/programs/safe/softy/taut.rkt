#lang racket

(define (taut b)
  (cond
   [(boolean? b) b]
   [else (and (taut (b #t)) (taut (b #f)))]))

(define prop/c
  ((or/c boolean? (boolean? . -> . (recursive-contract prop/c #:chaperone))) . -> . boolean?))

(provide/contract
 [taut prop/c]
 [prop/c any/c])
