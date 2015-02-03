#lang racket
(require soft-contract/fake-contract)

(define (insert x xs)
  (cond [(null? xs) (cons x null)]
        [(< x (car xs)) (cons x xs)]
        [else (cons (car xs) (insert x (cdr xs)))]))

(define (ordered? xs)
  (or (null? xs)
      (null? (cdr xs))
      (and (<= (car xs) (car (cdr xs)))
           (ordered? (cdr xs)))))

(define ordered-list/c (and/c (listof any/c) ordered?))

(provide
 (contract-out
  [ordered? ((listof real?) . -> . boolean?)]
  [insert (real? ordered-list/c . -> . ordered-list/c)]))
