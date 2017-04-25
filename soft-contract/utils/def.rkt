#lang typed/racket/base

(provide define-parameter :* define-syntax-id)

(require syntax/parse/define
         (for-syntax racket/base
                     (except-in racket/syntax format-symbol)
                     syntax/parse))

;; Shorthand for defining parameter
(define-syntax define-parameter
  (syntax-rules (:)
    [(_ x : τ v) (define x : (Parameterof τ) (make-parameter v))]))

;; declare the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))

(define-simple-macro (define-syntax-id id:id e)
  (define-syntax (id stx)
    (cond [(identifier? stx) #'e]
          [else
           (raise-syntax-error 'id "identifier macro expects no argument" stx)])))
