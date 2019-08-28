#lang racket

(require soft-contract/fake-contract)

(define f #:opaque)

(provide
 (contract-out
  [f (integer? . -> . integer?)]))
