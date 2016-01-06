#lang typed/racket/base

(provide define-data define-type/pred define-parameter :*)

(require
 (for-syntax racket/base racket/syntax syntax/parse))

;; Define type `t` along with predicate `t?`
(define-syntax (define-type/pred stx)
  (syntax-case stx ()
    [(_ τ e) (with-syntax ([τ? (format-id #'τ "~a?" #'τ)])
               #'(begin (define-type τ e)
                        (define-predicate τ? τ)))]))

;; define data-type hierarchy
(define-syntax-rule (define-data τ σ ...)
  (define-data′ τ (σ ...) ()))
(define-syntax (define-data′ stx)
  (syntax-case stx (subset: struct)
    [(_ τ () (σ ...)) #'(define-type/pred τ (U σ ...))]
    [(_ τ ((subset: τ′ clauses′ ...) clauses ...) (σ ...))
     #'(begin (define-data′ τ′ (clauses′ ...) ())
              (define-data′ τ (clauses ...) (τ′ σ ...)))]
    [(_ τ ((struct k f ...) clauses ...) (σ ...))
     #'(begin (struct k (f ...) #:transparent)
              (define-data′ τ (clauses ...) (k σ ...)))]
    [(_ τ (τ₁ clauses ...) (σ ...))
     #'(define-data′ τ (clauses ...) (τ₁ σ ...))]))

;; Shorthand for defining parameter
(define-syntax define-parameter
  (syntax-rules (:)
    [(_ x : τ v) (define x : (Parameterof τ) (make-parameter v))]))

;; define the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))
