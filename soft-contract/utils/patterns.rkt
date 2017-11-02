#lang typed/racket/base

(provide singleton-set)
(require racket/match
         racket/set)

(define (singleton-set? x) (and (set? x) (= 1 (set-count x))))

(define-match-expander singleton-set
  (syntax-rules ()
    [(_ p) (and (? singleton-set?) (app set-first p))]))
