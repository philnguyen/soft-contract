#lang soft-contract

(module lastpair racket
  (provide (contract-out [lastpair (cons? . -> . cons?)]))
  (define (lastpair x)
    (if (cons? #|HERE|# x) (lastpair (cdr x)) x)))
