#lang racket

(define f
  (case-lambda
    [(x) x]
    [(x y) (+ x y)]
    [(x y . z)
     (string-join (cons (number->string x) ; don't have real `list*` yet
                        (cons (number->string y)
                              (map number->string z)))
                  " + ")]))

(define f1 (f 42))
(define f2 (f 43 44))
(define f3 (f 45 46 47))

(provide
 (contract-out
  [f (parametric->/c (α)
       (case->
        [α . -> . α]
        [integer? . -> . integer?]
        [integer? integer? #:rest integer? . -> . string?]))]
  [f1 number?]
  [f2 number?]
  [f3 string?]))
