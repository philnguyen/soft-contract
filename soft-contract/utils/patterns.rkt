#lang typed/racket/base

(provide singleton-set with-guard match-lambda**/symmetry)
(require racket/match
         racket/set
         (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse))

(define (singleton-set? x) (and (set? x) (= 1 (set-count x))))

(define-match-expander singleton-set
  (syntax-rules ()
    [(_ p) (and (? singleton-set?) (app set-first p))]))

(define-syntax with-guard
  (syntax-rules ()
    [(_ () e ...) (let () e ...)]
    [(_ ([x eₓ] bnd ...) e ...) (let ([x eₓ])
                                  (and x (with-guard (bnd ...) e ...)))]))

(begin-for-syntax
  (define (dup-clause clauses)
    (append-map
     (syntax-parser
       [[(x y) body ...] (list #'[(x y) body ...]
                               #'[(y x) body ...])])
     clauses)))

(define-syntax match-lambda**/symmetry
  (syntax-parser
    [(_ clause ... #:else [p body ...])
     (with-syntax ([(clause* ...) (dup-clause (syntax->list #'(clause ...)))])
       #'(match-lambda**
           clause* ...
           [p body ...]))]))
