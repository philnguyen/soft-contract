#lang racket

(define weekday/c (and/c integer? exact? (>=/c 1) (<=/c 7)))
(define simple/c (or/c integer? symbol? boolean? string?))
(define v1 5)
(define v2 "6")
(define (id x) x)

(provide/contract
 [v1 weekday/c]
 [v2 simple/c]
 [id (weekday/c . -> . simple/c)])

