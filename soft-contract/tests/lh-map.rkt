#lang racket/base

(require soft-contract/fake-contract)

(define (map f xs)
  (cond [(pair? xs) (cons (f (car xs)) (map f (cdr xs)))]
        [else '()]))

(provide
 (contract-out
  [map ((any/c . -> . any/c #:total? #t) list? . -> . list? #:total? #t)]))
