#lang racket
(require soft-contract/fake-contract)

(define (f v l)
  (let ([x (member v l)])
    (if x (false? f) #f)))

(provide/contract
 [member (any/c (listof any/c) . -> . (or/c false? (nelistof any/c)))]
 [f (any/c (listof any/c) . -> . false?)])
