#lang racket

(define (string=>symbol s) (string->symbol s))

(provide
 (contract-out
  [string=>symbol (string? . -> . symbol?)]))
