#lang racket

(provide/contract (push (-> any/c list? list?)))

(define push cons)
