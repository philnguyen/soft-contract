#lang racket/base

(require (except-in racket/contract/base
                    -> ->i and/c or/c any/c list/c listof struct/c ->* provide/contract
                    one-of/c =/c >/c >=/c </c <=/c not/c)
         (for-syntax racket/base)
         racket/list)
(require (prefix-in c: racket/contract/base)
         (prefix-in r: racket/base))

(provide (all-from-out racket/contract/base) provide
         -> ->i and/c or/c any/c list/c listof struct/c ->* provide/contract contract-out
         dynamic-provide/contract
         dynamic->i
         dynamic-struct/c
         =/c >/c >=/c </c <=/c
         not/c)

(define-syntax (scv:ignore stx)
  (syntax-case stx ()
    [(_ s) (syntax-property #'s 'scv:ignore #t)]))

(define any/c c:any/c)
(define listof c:listof)
(define and/c c:and/c)
(define or/c c:and/c)
(define list/c c:list/c)
(define one-of/c c:one-of/c)
(define =/c c:=/c)
(define </c c:</c)
(define <=/c c:<=/c)
(define >/c c:>/c)
(define >=/c c:>=/c)
(define not/c c:not/c)
(define-syntax (struct/c stx) 
  (syntax-case stx ()
    [(_ name cs ...)
     #`(begin (dynamic-struct/c name cs ...)
              (scv:ignore (c:struct/c name cs ...)))]))
(define-syntax-rule (->i ([id ctc] ...) (_res (id* ...) result))
  (begin (dynamic->i (list (list 'id ctc) ...) (λ (id* ...) result))
         (scv:ignore (c:->i ([id ctc] ...) (_res (id* ...) result)))))

(define (dynamic->i doms result-f) (void))

(define (dynamic-struct/c . _) (void))

(define-syntax-rule (-> cs ... result-c) (dynamic->* #:mandatory-domain-contracts (list cs ...)
                                                     #:range-contracts (list result-c)))
(define-syntax-rule (->* (cs ...) #:rest rest-c result-c)
  (dynamic->* #:mandatory-domain-contracts (list cs ...)
              #:rest-contract rest-c
              #:range-contracts (list result-c)))

(define (dynamic-provide/contract . _) (void))

(define-syntax-rule (provide/contract [id ctc] ...)
  (begin (dynamic-provide/contract (list id ctc) ...)
         (scv:ignore (c:provide/contract [id ctc] ...))))

(require (for-syntax syntax/parse))

(define-syntax (provide stx)
  (syntax-parse stx #:literals (contract-out)
    [(_ (~or i:id (contract-out [p/i:id ctc:expr] ...)) ...)
     #'(begin (scv:ignore (r:provide i ... (contract-out [p/i ctc] ...) ...))
              (dynamic-provide/contract (list i any/c) ... (list p/i ctc) ... ...))]))
