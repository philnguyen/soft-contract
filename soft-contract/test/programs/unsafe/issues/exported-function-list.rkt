#lang racket

(module data racket
  (provide
   (contract-out [fs (listof (-> integer? integer?))]))
  (define fs (list add1)))

(require 'data)

(define f (car fs))
(f "")
