#lang racket
(require soft-contract/fake-contract)

(define (c? x) (and (integer? x) (> x 10)))
(define (f x) (f (+ x x)))

(provide (contract-out [f (c? . -> . c?)]))
