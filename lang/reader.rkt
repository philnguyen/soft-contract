#lang racket/base
(require "../check.rkt"
         (for-syntax racket/base))
(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         #%app #%datum #%top
         read read-syntax)

(define-syntax module-begin
  (syntax-rules (test)
    [(_) (#%module-begin)]
    [(_ m ... e) (#%module-begin (feedback '(m ... e)))]))

(define-syntax-rule (top-interaction . (m ... e))
  (#%top-interaction . (feedback '(m ... e))))
