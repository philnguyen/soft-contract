#lang racket

(require soft-contract/fake-contract)

(define (string=>symbol s) (string->symbol s))

(provide
 (contract-out
  [string=>symbol (string? . -> . any/c)]))
