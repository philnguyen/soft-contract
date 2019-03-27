#lang racket

(struct parent (name) #:transparent)
(struct child parent (age) #:transparent)

(define parent/c (struct/c parent string?))

(define (f) (child "foo" 42))
(define (g) (child "bar" 43))

(provide
 (contract-out
  [f (-> parent?)]
  [g (-> parent/c)]
  [child (string? integer? . -> . parent/c)]
  [child-age (child? . -> . integer?)]
  [parent-name (parent? . -> . string?)]))
