#lang racket/base

(provide absurd!
         (rename-out [strict-cond cond]
                     [strict-case case]))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract))

(begin-for-syntax
  (define/contract (mk-err tag stx)
    (symbol? syntax? . -> . syntax?)
    (with-syntax ([src (syntax-source stx)]
                  [line (syntax-line stx)]
                  [col (syntax-column stx)])
      #`(error '#,tag "reached supposedly unreachable code at ~a:~a:~a" src line col))))

(define-syntax absurd!
  (syntax-parser
    [stx:id
     (mk-err 'absurd #'stx)]))

(define-syntax strict-cond
  (syntax-parser
    [(_ clauses ... [(~literal else) e ...])
     #'(cond clauses ... [else e ...])]
    [(~and stx (_ clauses ...))
     (define/with-syntax err (mk-err 'cond #'stx))
     #'(cond clauses ... [else err])]))

(define-syntax strict-case
  (syntax-parser
    [(_ clauses ... [(~literal else) e ...])
     #'(case clauses ... [else e ...])]
    [(~and stx (_ clauses ...))
     (define/with-syntax err (mk-err 'case #'stx))
     #'(case clauses ... [else err])]))

