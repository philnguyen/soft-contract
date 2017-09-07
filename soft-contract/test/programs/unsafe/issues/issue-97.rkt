#lang racket/base
(require racket/contract)
(provide (contract-out (f (-> (or/c #f)))))

(define (f) #t)
