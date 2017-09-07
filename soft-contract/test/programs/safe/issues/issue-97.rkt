#lang racket/base
(require racket/contract)
(provide (contract-out (f (-> (or/c #t #f)))
                       (g (-> "hello" boolean?))))

(define (f) #t)
(define (g x) #t)
