#lang racket

(define (number=>string x) (number->string x))

(provide
 (contract-out
  [number=>string (number? . -> . string?)]))
