#lang racket/base

(require racket/contract)

(provide (contract-out (foo integer?)))

(define foo 1)
