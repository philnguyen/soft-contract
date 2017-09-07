#lang racket

(define (id x) x)

(define (use-map map)
  (map (λ (x) (/ 1 x)) '(42 43 44)))

(define (use-compose compose)
  ((compose add1 add1) 42))

(define (map f xs)
  (match xs
    ['() '()]
    [(cons x xs*) (cons (f x) (map f xs*))]))

(define (foldr f a xs)
  (match xs
    ['() a]
    [(cons x xs*) (f x (foldr f a xs*))]))

(define (foldl f a xs)
  (match xs
    ['() a]
    [(cons x xs*) (foldl f (f x a) xs*)]))

(define ((map-from-foldr foldr) f xs)
  (foldr (λ (x xs*)
           (cons (f x) xs*))
         '()
         xs))

(define ((compose f g) x) (f (g x)))

(define fold/c (parametric->/c (α β) ((α β . -> . β) β (listof α) . -> . β)))
(define map/c (parametric->/c (α β) ((α . -> . β) (listof α) . -> . (listof β))))

(provide
 (contract-out
  [id (parametric->/c (α) (α . -> . α))]
  [use-map (map/c . -> . (listof number?))]
  [use-compose
   ((parametric->/c (α β γ) ((β . -> . γ) (α . -> . β) . -> . (α . -> . γ)))
    . -> .
    exact-positive-integer?)]
  [map map/c]
  [foldr fold/c]
  [foldl fold/c]
  [map-from-foldr (fold/c . -> . map/c)]))
