#lang racket
(require soft-contract/fake-contract)

(define (recursive-div2 l)
  (if (empty? l) empty
      (cons (car l) (recursive-div2 (cdr (cdr l))))))

(provide/contract
   [recursive-div2 ((μ/c (X) (or/c empty? (cons/c any/c (cons/c any/c X))))
                    . -> . (listof any/c))])
