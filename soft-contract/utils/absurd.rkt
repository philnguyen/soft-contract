#lang racket/base

(provide absurd!
         (rename-out [strict-cond cond]
                     [strict-case case]))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-syntax (absurd! stx)
  (syntax-parse stx
    [_:id
     #'(absurd! absurd!)]
    [(_ tag:id)
     (define/with-syntax src (syntax-source stx))
     (define/with-syntax line (syntax-line stx))
     (define/with-syntax col (syntax-column stx))
     #'(error 'tag "unexpectedly reach ~a line ~a column ~a" src line col)]))

(define-syntax strict-cond
  (syntax-rules (else)
    [(_    clauses ... [else e ...])
     (cond clauses ... [else e ...])]
    [(_    clauses ...)
     (cond clauses ... [else (absurd! cond)])]))

(define-syntax strict-case
  (syntax-rules (else)
    [(_    clauses ... [else e ...])
     (case clauses ... [else e ...])]
    [(_    clauses ...)
     (case clauses ... [else (absurd! case)])]))
