#lang typed/racket/base

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/function
                     racket/contract
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "def-utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(begin-for-syntax

  (define-syntax-rule (with-hack:make-available (src id ...) e ...)
    (with-syntax ([id (format-id src "~a" 'id)] ...) e ...))

  (define-syntax-rule (hack:make-available src id ...)
    (begin (define/with-syntax id (format-id src "~a" 'id)) ...))

  ;; Global parameters that need to be set up for each `def`
  (define-parameter/contract
    ; identifiers available to function body
    [-o identifier? #f]
    [-ℓ identifier? #f]
    [-Ws identifier? #f]
    [-⟪ℋ⟫ identifier? #f]
    [-$ identifier? #f]
    [-Γ identifier? #f]
    [-Σ identifier? #f]
    [-⟦k⟧ identifier? #f]
    [-sig syntax? #f]
    [-Wⁿ (listof identifier?) #f]
    [-Wᵣ (or/c #f identifier?) #f]
    )

  (define/contract (gen-arity-check body)
    ((listof syntax?) . -> . (listof syntax?))

    (define/contract (sig->ok-arities sig)
      (syntax? . -> . procedure-arity?)
      (define (syntax-length stx) (length (syntax->list stx)))
      (syntax-parse sig
        [((~literal ->) c ... _) (length (syntax->list #'(c ...)))]
        [((~literal ->*) c ... #:rest _ _) (arity-at-least (syntax-length #'(c ...)))]
        [((~literal case->) clauses ...)
         (for/list ([clause (in-syntax-list #'(clauses ...))])
           (syntax-parse clause
             [((~literal ->) c ... #:rest _ _) (arity-at-least (syntax-length #'(c ...)))]
             [((~literal ->) c ... _) (syntax-length #'(c ...))]))]
        [((~literal ∀/c) _ c) (sig->ok-arities #'c)]))
    (define/with-syntax ok-arity
      (let go ([arity (normalize-arity (sig->ok-arities (-sig)))])
        (match arity
          [(arity-at-least n) #`(arity-at-least #,n)]
          [(? list? l) #`(list #,@(map go l))]
          [(? number? n) n])))
    (define/with-syntax error-msg (string->symbol (format "arity ~a" (syntax->datum #'ok-arity))))
    
    (list
     #`(define num-args (length #,(-Ws)))
     #`(cond
         [(arity-includes? ok-arity num-args)
          #,@body]
         [else
          (define blm (-blm (ℓ-src #,(-ℓ)) '#,(-o) (list 'error-msg) (map -W¹-V #,(-Ws)) #,(-ℓ)))
          (#,(-⟦k⟧) blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))])))

  (define/contract (gen-domain-checks body)
    ((listof syntax?) . -> . (listof syntax?))
    (list #`(error 'gen-domain-checks "TODO: ~a" #,(pretty-format (map syntax->datum body)))))

  (define/contract (gen-range-checks body)
    ((listof syntax?) . -> . (listof syntax?))
    (list #`(error 'gen-range-checks "TODO: ~a" #,(pretty-format (map syntax->datum body)))))
  )
