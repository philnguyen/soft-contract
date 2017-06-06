#lang racket

(require "b.rkt")

(define (g x)
  (f (f x)))

(provide (contract-out (g (-> integer? integer?))))
