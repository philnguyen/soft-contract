#lang racket
;; module2.rkt
(require "module1.rkt")
(define (add a b)
  (+ (id a) (id b)))
(provide (contract-out [add (-> exact-integer? exact-integer? exact-integer?)]))
