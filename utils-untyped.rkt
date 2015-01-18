#lang racket/base

(provide (all-defined-out))

(define (todo x)
  (error 'TODO "~a" x))
