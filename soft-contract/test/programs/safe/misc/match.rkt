#lang racket

(define (f x)
  (if (cons? x)
      (car x)
      (if (char? x) 42 (add1 ""))))

(provide
 (contract-out
  [f ((or/c (cons/c real? any/c) char?) . -> . number?)]))
