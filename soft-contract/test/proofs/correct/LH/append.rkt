#lang racket/base

(require racket/match
         racket/contract
         soft-contract/induction)

;; Source
;; https://github.com/ucsd-progsys/liquidhaskell/blob/develop/benchmarks/popl18/ple/pos/Append.hs

(define append
  (match-lambda**
   [('()         ys) ys]
   [((cons x xs) ys) (cons x (append xs ys))]))

(define map
  (match-lambda**
   [(f '()        ) '()]
   [(f (cons x xs)) (cons (f x) (map f xs))]))

(define concat-map
  (match-lambda**
   [(f '()        ) '()]
   [(f (cons x xs)) (append (f x) (concat-map f xs))]))

(define concatt
  (match-lambda
    ['()         '()]
    [(cons x xs) (append x (concatt xs))]))

(define-theorem thm:append-neutral
  (∀/c {α} (∀ ([xs (listof α)]) (equal? (append xs '()) xs)))
  #:proof
  (λ (xs)
    (trivial-list-induct xs (λ (xs) (↑ (equal? (append xs '()) xs))))))

(define-theorem thm:append-assoc
  (∀/c {α}
    (∀ ([xs ys zs (listof α)])
       (equal? (append (append xs ys) zs) (append xs (append ys zs)))))
  #:proof
  (λ (xs ys zs)
    (trivial-list-induct
     xs
     (λ (xs) (↑ (equal? (append (append xs ys) zs) (append xs (append ys zs))))))))

(define-theorem thm:map-append
  (∀/c {α}
    (∀ ([f (α . -> . α)] [xs ys (listof α)])
       (equal? (map f (append xs ys)) (append (map f xs) (map f ys)))))
  #:proof
  (λ (f xs ys)
    (trivial-list-induct
     xs
     (λ (xs) (↑ (equal? (map f (append xs ys)) (append (map f xs) (map f ys))))))))

(define-theorem thm:concat-map
  (∀/c {α}
    (∀ ([f (α . -> . (listof (listof α)))] [xs (listof α)])
       (equal? (concatt (map f xs)) (concat-map f xs))))
  #:proof
  (λ (f xs)
    (trivial-list-induct
     xs
     (λ (xs) (↑ (equal? (concatt (map f xs)) (concat-map f xs)))))))
