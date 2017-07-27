#lang racket

(define (f)
  (hash 1 1))

(provide (contract-out (f (-> (hash/c integer? integer?)))))
