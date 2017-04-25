#lang racket
(require soft-contract/fake-contract)

(define (append xs ys)
  (if (empty? xs) ys
      (cons (car xs) (append (cdr xs) ys))))

(provide/contract
   [append (#|HERE|# any/c (listof any/c) . -> . (listof any/c))])
