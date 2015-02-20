#lang racket
(require soft-contract/fake-contract)

(define (all p? xs)
  (cond
   [(empty? xs) #t]
   [(empty? (cdr xs)) (p? (car xs))]
   [else (and (p? (car xs)) (all p? (cdr xs)))]))

(provide/contract [all ((any/c . -> . any/c) (listof any/c) . -> . any/c)])
