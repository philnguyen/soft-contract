#lang racket

(define (f)
  (hash))

(provide (contract-out (f (-> (hash/c integer? integer?)))))
