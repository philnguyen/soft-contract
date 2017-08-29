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

(provide
 (contract-out
  [id (parametric->/c (α) (α . -> . α))]
  [use-map
   ((parametric->/c (α β) ((α . -> . β) (listof α) . -> . (listof β)))
    . -> .
    (listof number?))]
  [use-compose
   ((parametric->/c (α β γ) ((β . -> . γ) (α . -> . β) . -> . (α . -> . γ)))
    . -> .
    exact-positive-integer?)]
  [map (parametric->/c (α β) ((α . -> . β) (listof α) . -> . (listof β)))]
  [foldr (parametric->/c (α β) ((α β . -> . β) β (listof α) . -> . β))]
  [foldl (parametric->/c (α β) ((α β . -> . β) β (listof α) . -> . β))]
  [map-from-foldr ((parametric->/c (α β) ((α β . -> . β) β (listof α) . -> . β))
                   . -> .
                   (parametric->/c (α β) ((α . -> . β) (listof α) . -> . (listof β))))]))
