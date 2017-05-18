#lang racket

(require "helper-1.rkt"
         "helper-2.rkt")

(provide
 (contract-out
  [number=>symbol (number? . -> . symbol?)]))

(define (number=>symbol n)
  (string=>symbol (number=>string n)))
