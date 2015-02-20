#lang racket
(require soft-contract/fake-contract)

(define (lastpair x)
  (if (cons? (cdr x)) (lastpair (cdr x)) x))

(provide/contract [lastpair (cons? . -> . cons?)])
