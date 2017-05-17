#lang racket

(define n1 (apply + '(1 2 3)))

(define n2 (apply (λ (x y) (+ x y)) (list 1 2)))

(define n3 (apply (λ (x y . z) (+ x y (length z))) (list 1 2 3 4 5)))

(define n4 (apply (λ (x y . z) (+ x y (length z))) 1 2 3 (list 4 5)))

(provide
 (contract-out
  [n1 exact-integer?]
  [n2 exact-integer?]
  [n3 exact-integer?]
  [n4 exact-integer?]))




