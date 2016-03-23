#lang racket
(require soft-contract/fake-contract)

(define (f member v l)
  (let ([x (member v l)])
    (if x (false? f) #f)))

(provide/contract
 [f ((any/c (listof any/c) . -> . (or/c false? (cons/c any/c (listof any/c))))
     any/c
     (listof any/c)
     . -> . false?)])
