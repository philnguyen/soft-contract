#lang racket

(define (f x) (* x 2))
(define ((g x) y)
  (cons (f x) (f y)))

(provide/contract
 [f ((>=/c 0) . -> . (>=/c 0))]
 [g (->i ([x (>=/c 0)])
         [res (x)
              (->i ([y (>=/c x)])
                   [res (y)
                        (λ (p)
                          (>= (cdr p) (car p)))])])])
