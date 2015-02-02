;; 1421368695192

#lang racket
(require soft-contract/fake-contract)

(define (f x) 5)

(provide (contract-out [f ((and/c integer? string?) . -> . string?)]))
