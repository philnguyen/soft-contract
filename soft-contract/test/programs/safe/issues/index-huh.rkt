#lang racket/base

(require (only-in typed/racket/base index?)
         (only-in (submod (lib "typed-racket/private/type-contract.rkt") predicates) nonnegative?)
         racket/contract/base)

(define (f x) (if (index? x) (+ 1 x) 42))
(define c nonnegative?)
(define (g x) (if (nonnegative? x) x 42))

(provide
 (contract-out
  [f (any/c . -> . exact-nonnegative-integer?)]
  [g (nonnegative? . -> . nonnegative?)]))
