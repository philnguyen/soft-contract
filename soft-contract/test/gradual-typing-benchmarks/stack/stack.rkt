#lang racket/base

(provide
 init
 push
)


(define (init)
  '())

(define (push st i)
  (cons i st))
