#lang racket/base

(require racket/contract)
(require "data-adaptor.rkt")
(define p (foo))

(provide
 (contract-out
  [p foo?]))
