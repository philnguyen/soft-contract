#lang racket/base

(require soft-contract/fake-contract)

(define (foldr op a xs) (if (null? xs) a (op (car xs) (foldr op a (cdr xs)))))
(define (foldl op a xs) (if (null? xs) a (foldl op (op (car xs) a) (cdr xs))))
(define (reverse xs) (foldl (λ (ys x) (cons x ys)) '() xs))
(define (@ xs ys) (foldr cons xs ys))
(define (concat xss) (foldr @ '() xss))

(provide
 (contract-out
  [foldr ((any/c any/c . -> . any/c) any/c list? . -> . any/c #:total? #t)]
  [foldl ((any/c any/c . -> . any/c) any/c list? . -> . any/c #:total? #t)]
  [reverse (list? . -> . list? #:total? #t)]
  [@ (list? list? . -> . list? #:total? #t)]
  [concat ((listof list?) . -> . list? #:total? #t)]))
