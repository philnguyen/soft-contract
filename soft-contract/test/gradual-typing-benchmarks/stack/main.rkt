#lang racket/base

(require "stack.rkt")

(define (main N)
  (for/fold ([st (init)])
            ([i (in-range N)])
    (push st i))
  (void))

(time (main 60000))
