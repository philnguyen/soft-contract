#lang racket/base

(provide (all-defined-out))

(define (in-syntax-list stx) (in-list (syntax->list stx)))
