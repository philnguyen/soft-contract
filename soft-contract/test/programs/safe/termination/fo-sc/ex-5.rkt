#lang racket/base

(require soft-contract/fake-contract)

(define (f x y)
  (cond
    [(null? y) x]
    [(null? x) (f y (cdr y))]
    [else (f y (cdr x))]))

(provide
 (contract-out
  [f (list? list? . -> . any/c #:total? #t)]))
