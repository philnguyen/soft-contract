#lang racket
(require soft-contract/fake-contract)

(define (subst* new old t)
  (cond
   [(equal? old t) new]
   [#|HERE|# else (cons (subst* new old (car t))
                        (subst* new old (cdr t)))]))

(provide/contract [subst* (any/c any/c any/c . -> . any/c)])
