#lang racket/base

(require soft-contract/fake-contract)

(define (rev ls) (r1 ls '()))
(define (r1 ls a) (if (null? ls) a (r1 #|HERE|# ls (cons (car ls) a))))

(provide
 (contract-out
  [rev (list? . -> . list? #:total? #t)]))
