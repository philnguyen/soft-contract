#lang racket

(define h0 (hasheq))
(define h1 (hash 1 2))
(define h1.count (hash-count h1))
(define h11 (hash-set (hash-set h1 1 2) 2 3))
(define h11.count (hash-count h11))
(define h11.1 (hash-ref h11 1))
(define h11.5 (hash-ref h11 5)) ; doesn't catch key-not-found
(define h2 (hash-remove h11 1))
(define h2.1 (hash-ref h2 1)) ; doesn't catch key-not-found
(define h3 (hash-set h11 3 "string"))
(define h3.5 (hash-ref h3 5)) ; doesn't catch key-not-found
(define m0 (make-immutable-hash '()))
(define m (make-hash (list (cons 1 2) (cons 3 4) (cons 5 "string"))))
(hash-remove! m 5)
(define k (hash-ref m 5)) ; doesn't catch key-not-found

(provide
 (contract-out
  [h0 (hash/c none/c none/c)]
  [h1 hash?]
  [h1.count exact-nonnegative-integer?]
  [h11 (hash/c integer? integer?)]
  [h11.count exact-nonnegative-integer?]
  [h11.1 integer?]
  [h11.5 integer?]
  [h2 (hash/c integer? integer?)]
  [h2.1 integer?]
  [h3 (hash/c integer? (or/c integer? string?))]
  [h3.5 (or/c string? integer?)]
  [m0 (hash/c none/c none/c)]
  [m (hash/c integer? (or/c integer? string?))]
  [k (or/c string? integer?)]
))
