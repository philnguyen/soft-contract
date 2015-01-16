#lang racket/base

(require (except-in racket/contract/base
                    -> ->i and/c or/c any/c list/c listof struct/c ->*)
         (for-syntax racket/base)
         racket/list)
(require (prefix-in c: racket/contract/base))

(provide (all-from-out racket/contract/base)
         -> ->i and/c or/c any/c list/c listof struct/c ->*)

(define-syntax (scv:ignore stx)
  (syntax-case stx ()
    [(_ s) (syntax-property #'s 'scv:ignore #t)]))

(define any/c c:any/c)
(define listof c:listof)
(define and/c c:and/c)
(define or/c c:and/c)
(define list/c c:list/c)
(define-syntax (struct/c stx) 
  (syntax-case stx ()
    [(_ name cs ...)
     #`(begin (dynamic-struct/c (quote-syntax name) cs ...)
              (scv:ignore (c:struct/c name cs ...)))]))
(define-syntax-rule (->i ([id ctc] ...) (res (id* ...) result))
  (begin (dynamic->i (list ctc ...) (λ (id* ...) result))
         (scv:ignore (c:->i ([id ctc] ...) (res (id* ...) result)))))

(define (dynamic->i doms result-f) (void))

(define (dynamic-struct/c . _) (void))

(define-syntax-rule (-> cs ... result-c) (dynamic->* #:mandatory-domain-contracts (list cs ...)
                                                     #:range-contracts (list result-c)))
(define-syntax-rule (->* (cs ...) #:rest rest-c result-c)
  (dynamic->* #:mandatory-domain-contracts (list cs ...)
              #:rest-contract rest-c
              #:range-contracts (list result-c)))
