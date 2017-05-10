#lang racket

(define (f x y) (values y x y))

(define c (-> integer? string? (if (< 1 2) (values string? integer? string?) (values))))

(provide
 (contract-out [f c]))
