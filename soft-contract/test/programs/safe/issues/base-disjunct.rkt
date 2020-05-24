#lang racket

(define c (or/c #f #t))
(define u #f)
(define v #t)

(define boxed-c (list/c (list/c (list/c c))))
(define (id x) x)

(provide
 (contract-out [u c]
               [v c]
               [id (boxed-c . -> . boxed-c)]))
