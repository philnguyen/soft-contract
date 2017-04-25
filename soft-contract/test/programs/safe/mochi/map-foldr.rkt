#lang racket
(require soft-contract/fake-contract)

(define (foldr f z xs)
  (if (empty? xs) z
      (f (car xs) (foldr f z (cdr xs)))))

(define (map f xs)
  (foldr (λ (x ys) (cons (f x) ys)) empty xs))

(provide/contract
 [foldr ((any/c any/c . -> . any/c) any/c (listof any/c) . -> . any/c)]
 [map ((any/c . -> . any/c) (listof any/c) . -> . (listof any/c))])
