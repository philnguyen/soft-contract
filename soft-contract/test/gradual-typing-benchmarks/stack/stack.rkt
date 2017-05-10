#lang racket

(require soft-contract/fake-contract)

(provide (contract-out
          [init (-> list?)]
          [push (-> list? any/c list?)]))

(define (init)
  '())

(define (push st i)
  (cons i st))
