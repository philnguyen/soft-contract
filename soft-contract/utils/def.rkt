#lang typed/racket/base

(provide ::= define-type/pred define-parameter :*)

(require
 (for-syntax racket/base racket/syntax syntax/parse))

;; Define type `t` along with predicate `t?`
(define-syntax (define-type/pred stx)
  (syntax-case stx ()
    [(_ τ e) (with-syntax ([τ? (format-id #'τ "~a?" #'τ)])
               #'(begin (define-type τ e)
                        (define-predicate τ? τ)))]))

;; define data-type hierarchy
(define-syntax-rule (τ . ::= . σ ...)
  (τ . ::=/ac . (σ ...) ()))
(define-syntax (::=/ac stx)
  (syntax-parse stx
    #:literals (struct :)
    [(_ τ () (σ ...)) #'(define-type/pred τ (U σ ...))]
    [(_ τ ((τ₀ . (~literal ::=*) . clauses₀ ...) clauses ...) (σ ...))
     #'(begin (τ₀ . ::=/ac . (clauses₀ ...) ())
              (τ  . ::=/ac . (clauses ...) (τ₀ σ ...)))]
    [(_ τ ((struct k [f : t] ...) clauses ...) (σ ...))
     #'(begin (struct k ([f : t] ...) #:transparent)
              (τ . ::=/ac . (clauses ...) (k σ ...)))]
    [(_ τ ((struct k [ts ...]) clauses ...) (σ ...))
     (define fields
       (for/list ([(t i) (in-indexed (syntax->list #'(ts ...)))])
         (define x (string->symbol (format "x_~a" i)))
         #`(#,x : #,t)))
     #`(begin (struct k #,fields #:transparent)
              (τ . ::=/ac . (clauses ...) (k σ ...)))]
    [(_ τ (τ₁ clauses ...) (σ ...))
     #'(τ . ::=/ac . (clauses ...) (τ₁ σ ...))]))

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
