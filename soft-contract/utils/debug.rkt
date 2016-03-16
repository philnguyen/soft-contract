#lang typed/racket/base

(provide debugs with-debug dbg todo)

(require "set.rkt" "def.rkt")

(define-parameter debugs : (℘ Symbol) ∅)

(define-syntax-rule (with-debug t e ...)
  (parameterize ([debugs (set-add (debugs) t)]) e ...))

(: dbg : Symbol String Any * → Void)
(define (dbg t fmt . xs)
  (when (∋ (debugs) t)
    (apply printf fmt xs)))

(define (todo x) (error 'TODO "~a" x))
