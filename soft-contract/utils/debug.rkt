#lang typed/racket/base

(provide debugs with-debug dbg todo)

(require "set.rkt")

(define debugs : (Parameterof (Setof Symbol)) (make-parameter ∅))

(define-syntax-rule (with-debug t e ...)
  (parameterize ([debugs (set-add (debugs) t)]) e ...))

(: dbg : Symbol String Any * → Void)
(define (dbg t fmt . xs)
  (when (∋ (debugs) t)
    (apply printf fmt xs)))

(define (todo x) (error 'TODO "~a" x))
