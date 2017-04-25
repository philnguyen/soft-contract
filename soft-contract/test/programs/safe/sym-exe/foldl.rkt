#lang racket
(require soft-contract/fake-contract)

(define (foldl f z xs)
  (if (empty? xs) z
      (foldl f (f (car xs) z) (cdr xs))))

(provide/contract
 [foldl ((any/c any/c . -> . any/c) any/c (listof any/c) . -> . any/c)])
