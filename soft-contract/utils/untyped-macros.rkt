#lang racket/base
(require
 racket/match racket/contract racket/list
 (for-syntax racket/base syntax/parse))

;; Macros defined in typed modules can't be used in untyped modules,
;; hence this module.
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pattern matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (match? v p ...) (match v [p #t] ... [_ #f]))
(define-syntax-rule (match-λ? p ...) (match-lambda [p #t] ... [_ #f]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Augmented definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate a temporary hacky helper
(define-syntax-rule (define/hack (f x ...) e ...)
  (define (f x ...)
    (printf "FIXME: get rid of `~a` hack~n" (quote f))
    e ...))
