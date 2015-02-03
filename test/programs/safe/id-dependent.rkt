#lang racket
(require soft-contract/fake-contract)

(define (f x) x)

(provide/contract [f (->i ([x number?]) (res (x) (=/c x)))])
