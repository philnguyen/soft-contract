#lang racket

(define (push x st) (cons x st))

(provide/contract
 [push (any/c list? . -> . list?)])
