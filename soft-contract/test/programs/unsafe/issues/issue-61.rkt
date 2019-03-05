#lang racket

(define (f x y) (values y x))

(define c (-> integer? string? (values string? integer? string?)))

(provide
 (contract-out [f c]))
