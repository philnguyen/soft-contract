#lang racket/base

(require (except-in racket/set set/c)
         soft-contract/fake-contract)

(define s (set 1 2 "4"))

(provide
 (contract-out
  [s (set/c integer?)]))
