#lang racket

(module a racket
  (define (id x) x)
  (provide
   (contract-out
    (id (-> exact-integer? exact-integer?)))))
(require 'a)
(provide
 (contract-out
  [id (-> string? string?)]))
