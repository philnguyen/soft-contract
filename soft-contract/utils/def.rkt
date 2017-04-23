#lang typed/racket/base

(provide ::= define-type/pred define-parameter :* define-syntax-id)

(require syntax/parse/define
         (for-syntax racket/base
                     (except-in racket/syntax format-symbol)
                     syntax/parse
                     "pretty.rkt"))

;; Define type `t` along with predicate `t?`
(define-syntax (define-type/pred stx)
  (syntax-case stx ()
    [(_ τ e) (with-syntax ([τ? (format-id #'τ "~a?" #'τ)])
               #'(begin (define-type τ e)
                        (define-predicate τ? τ)))]))

(begin-for-syntax
  (define-syntax-class sid
    #:description "identifier prefixed with `-`"
    (pattern id
       #:fail-unless
       (regexp-match? #rx"-.+" (symbol->string (syntax-e #'id)))
       "struct name must be prefixed with `-`")))

;; define data-type hierarchy
(define-syntax-rule (τ . ::= . σ ...)
  (τ . ::=/ac . (σ ...) ()))
(define-syntax (::=/ac stx)
  (syntax-parse stx
    #:literals (quote)
    [(_ τ () (σ))
     #'(define-type/pred τ σ)]
    [(_ τ () (σ ...))
     #'(define-type/pred τ (U σ ...))]
    [(_ τ ((quote s) clauses ...) (σ ...))
     #'(τ . ::=/ac . (clauses ...) ((quote s) σ ...))]
    [(_ τ ((k:sid fs ...) clauses ...) (σ ...))
     (define fields
       (for/list ([(f i) (in-indexed (syntax->list #'(fs ...)))])
         (syntax-parse f
           [(_ (~literal :) _) f]
           [t
            (define x (format-symbol "~a" (n-sub i)))
            #`(#,x : t)])))
     #`(begin (struct k #,fields #:transparent)
              (τ . ::=/ac . (clauses ...) (k σ ...)))]
    [(_ τ (τ₁ clauses ...) (σ ...))
     #'(τ . ::=/ac . (clauses ...) (τ₁ σ ...))]))

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
