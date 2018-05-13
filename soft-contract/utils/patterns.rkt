#lang typed/racket/base

(provide singleton-set with-guard)
(require racket/match
         racket/set)

(define (singleton-set? x) (and (set? x) (= 1 (set-count x))))

(define-match-expander singleton-set
  (syntax-rules ()
    [(_ p) (and (? singleton-set?) (app set-first p))]))

(define-syntax with-guard
  (syntax-rules ()
    [(_ () e ...) (let () e ...)]
    [(_ ([x eₓ] bnd ...) e ...) (let ([x eₓ])
                                  (and x (with-guard (bnd ...) e ...)))]))
