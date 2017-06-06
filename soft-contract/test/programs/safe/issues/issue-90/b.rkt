#lang typed/racket/base

(: f (-> Integer Integer))
(define (f x)
  (+ x 2))

(provide f)
