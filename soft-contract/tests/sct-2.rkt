#lang racket/base

(require soft-contract/fake-contract)

(define (f i x) (if (null? i) x (g (cdr i) x i)))
(define (g a b c) (f a (cons b c)))

(provide
 (contract-out
  [f (list? any/c . -> . any/c #:total? #t)]))
