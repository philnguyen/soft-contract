#lang racket
(require soft-contract/fake-contract)

(define (eq x) x)
(define (succ x) (add1 x))
(define (succ2 x) (add1 x))
(define (mult x y) (* x y))
(define (mult2 x y) (* x y))

(provide/contract
 [  eq  (->i ([x number?]) (res (x) (=/c x)))]
 [succ  (->i ([x number?]) (res (x) (=/c (add1 x))))]
 [succ2 (->i ([x number?]) (res (x) (lambda (z) (= x (sub1 z)))))]
 [mult  (->i ([x number?] [y number?]) (res (x y) (=/c (* x y))))]
 ;; reverse order of mult in contract from implementation
 [mult2 (->i ([x number?] [y number?]) (res (x y) (=/c (* y x))))])
