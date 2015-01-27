#lang racket
(require soft-contract/fake-contract)

(define (lastpair x)
  (if (cons? #|HERE|# x) (lastpair (cdr x)) x))

(provide/contract
 [lastpair (cons? . -> . cons?)])
