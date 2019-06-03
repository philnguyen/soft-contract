#lang racket/base

(require soft-contract/fake-contract)

(define (f a b)
  (if (null? b)
      (g a '())
      (f (cons (car b) a) (cdr b))))

(define (g c d)
  (if (null? c)
      d
      (g #|HERE|# c (cons (car c) d))))

(provide
 (contract-out
  [f (list? list? . -> . any/c #:total? #t)]))
