#lang racket
(require soft-contract/fake-contract)

(define (f x) x)

(provide/contract [f (->i ([x real?]) (res (x) (=/c x)))])
