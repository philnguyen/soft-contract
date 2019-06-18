#lang racket

(require "m3.rkt")

(define p (posn 42))

(provide
 (contract-out
  [p posn?]))
