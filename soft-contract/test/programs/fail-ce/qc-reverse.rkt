#lang racket
(require soft-contract/fake-contract)

(define (rev xs)
  (cond [(null? xs) null]
        [else (app (rev (cdr xs)) (cons (car xs) null))]))

(define (app xs ys)
  (cond [(null? xs) ys]
        [else (cons (car xs) (app (cdr xs) ys))]))

(define (prop xs ys)
  (equal? (rev (app xs ys))
          (app (rev xs) (rev ys))))

(provide
 (contract-out
  [prop ((listof any/c) (listof any/c) . -> . (not/c false?))]))
