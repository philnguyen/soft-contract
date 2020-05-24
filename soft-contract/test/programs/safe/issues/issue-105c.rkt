#lang racket
;; struct-access-2.rkt

(require "issue-105b.rkt")

(define (getx f)
  (foo-x f))

(provide (contract-out (getx (-> foo? exact-integer?))))
