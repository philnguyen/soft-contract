#lang racket

(define (recursive-div2 l)
  (if (empty? l) empty
      (cons (car l) (recursive-div2 (cdr (cdr l))))))

(define even-list/c
  (or/c null? (cons/c any/c (cons/c any/c (recursive-contract even-list/c #:flat)))))

(provide/contract
 [recursive-div2 (even-list/c . -> . (listof any/c))])
