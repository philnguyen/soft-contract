#lang racket/base

(require (except-in racket/contract
                    flat-contract
                    -> ->i case-> and/c or/c any/c none/c list/c listof struct/c ->* provide/contract
                    one-of/c =/c >/c >=/c </c <=/c between/c not/c cons/c box/c vector/c vectorof hash/c
                    recursive-contract)
         (except-in racket/set set/c)
         (for-syntax racket/base racket/string racket/syntax syntax/parse)
         racket/list)
(require (prefix-in c: racket/contract/base)
         (prefix-in c: (only-in racket/set set/c))
         (prefix-in r: racket/base))

(provide (all-from-out racket/contract/base) provide
         flat-contract
         -> ->i case-> and/c or/c any/c none/c list/c listof struct/c ->* provide/contract contract-out false/c
         recursive-contract
         (rename-out [c:any any]
                     [c:hash/c hash/c]
                     [c:set/c set/c])
         dynamic-provide/contract
         dynamic->i dynamic->* dynamic-case-> 
         dynamic-struct/c
         dynamic-recursive-contract
         dynamic-struct-out
         =/c >/c >=/c </c <=/c between/c
         not/c cons/c
         one-of/c box/c vector/c vectorof
         define/contract
         dynamic-mon)

(define-syntax (scv:ignore stx)
  (syntax-case stx ()
    [(_ s) (syntax-property #'s 'scv:ignore #t)]))

(define flat-contract c:flat-contract)
(define any/c c:any/c)
(define none/c c:none/c)
(define listof c:listof)
(define and/c c:and/c)
(define or/c c:or/c)
(define list/c c:list/c)
(define one-of/c c:one-of/c)
(define =/c c:=/c)
(define </c c:</c)
(define <=/c c:<=/c)
(define >/c c:>/c)
(define >=/c c:>=/c)
(define between/c c:between/c)
(define not/c c:not/c)
(define cons/c c:cons/c)
(define box/c c:box/c)
(define vector/c c:vector/c)
(define vectorof c:vectorof)
(define false/c c:false/c)
(define-syntax (struct/c stx) 
  (syntax-case stx ()
    [(_ name cs ...)
     #`(begin (dynamic-struct/c name cs ...)
              (scv:ignore (c:struct/c name cs ...)))]))
(define dynamic->* c:dynamic->*)
(define-syntax-rule (->i ([id ctc] ...) (_res (id* ...) result))
  (begin (dynamic->i (list (list 'id ctc) ...) (λ (id* ...) result))
         (scv:ignore (c:->i ([id ctc] ...) (_res (id* ...) result)))))

(define (dynamic->i doms result-f) (void))

(define (dynamic-struct/c . _) (void))

(define (dynamic-struct-out . _) (void))

(define-syntax ->
  (syntax-rules (c:any)
    [(-> cs ... c:any)
     (dynamic->* #:mandatory-domain-contracts (list cs ...)
                 #:range-contracts #f)]
    [(-> cs ... result-c)
     (dynamic->* #:mandatory-domain-contracts (list cs ...)
                 #:range-contracts (list result-c))]))
(define-syntax ->*
  (syntax-rules (c:any)
    [(->* (cs ...) #:rest rest-c c:any)
     (dynamic->* #:mandatory-domain-contracts (list cs ...)
                 #:rest-contract rest-c
                 #:range-contracts #f)]
    [(->* (cs ...) #:rest rest-c result-c)
     (dynamic->* #:mandatory-domain-contracts (list cs ...)
                 #:rest-contract rest-c
                 #:range-contracts (list result-c))]))
(define-syntax case->
  (syntax-rules ()
    [(_ clauses ...)
     (begin
       (case->/acc () (clauses ...))
       ;; TODO can't enable below yet, because hacky expansion replaces `->` and `->*`
       #;(scv:ignore (c:case-> clauses ...)))]))

(define-syntax case->/acc
  (syntax-rules (c:any)
    [(_ (ctcs ...) ())
     (dynamic-case-> ctcs ...)]
    [(_ (ctcs ...) ((_ init ... #:rest rest c:any) clauses ...))
     (case->/acc (ctcs ... (list (list init ...) rest #f))
                 (clauses ...))]
    [(_ (ctcs ...) ((_ init ... #:rest rest range) clauses ...))
     (case->/acc (ctcs ... (list (list init ...) rest (list range)))
                 (clauses ...))]
    [(_ (ctcs ...) ((_ init ... c:any) clauses ...))
     (case->/acc (ctcs ... (list (list init ...) #f #f))
                 (clauses ...))]
    [(_ (ctcs ...) ((_ init ... range) clauses ...))
     (case->/acc (ctcs ... (list (list init ...) #f (list range)))
                 (clauses ...))]))

(define (dynamic-case-> . _) (void))

(define (dynamic-provide/contract . _) (void))

(define-syntax-rule (provide/contract [id ctc] ...)
  (begin (dynamic-provide/contract (list id ctc) ...)
         (scv:ignore (c:provide/contract [id ctc] ...))))

(define-syntax define/contract
  (syntax-parser
    [(_ x:id c:expr e:expr)
     #'(define x (dynamic-mon 'x 'module c e))]
    [(_ (f:id x:id ...) c:expr e:expr ...)
     #'(define/contract f c (λ (x ...) e ...))]))

(define (dynamic-mon . xs) (void))

(require (for-syntax syntax/parse))

(define-syntax (provide stx)
  (syntax-parse stx #:literals (contract-out struct struct-out)
    [(_ (~or i:id
             (struct-out so:id)
             (contract-out (~or [p/i:id ctc:expr]
                                ;; TODO confirm that ignoring super struct declaration here makes no difference.
                                ;; In a transparent module, the superstruct relation is recorded at struct definition site.
                                [struct (~or s:id (s:id _:id)) ([ac:id dom:expr] ...)]) ...))
        ...)
     (define (ids->str ids)
       (string-join (map symbol->string (map syntax-e (syntax->list ids)))))
     #;(unless (null? (syntax->list #'(i ...)))
       (printf "Warning: ignore verifying: ~a~n" (ids->str #'(i ...))))
     #;(unless (null? (syntax->list #'(so ...)))
       (printf "Warning: ignore verifying `struct-out` form(s) for: ~a~n" (ids->str #'(so ...))))
     #'(begin
         ;; Real stuff to preserve the program's meaning when run
         (scv:ignore
          (r:provide i ...
                     (struct-out so) ...
                     (contract-out [p/i ctc] ...
                                   [struct s ([ac dom] ...)] ...)
                     ...))
         ;; Things to give to SCV for verification.
         ;; Ignore all non-contracted identifiers because they might be macros even.
         ;; Verifying against `any/c` doesn't mean much anyways
         (dynamic-provide/contract
          i ...
          (list p/i ctc) ... ...
          (dynamic-struct-out 's (list 'ac dom) ...) ... ...))]))

;; Phil's clueless hack for `recursive-contract`
(define-syntax-rule (recursive-contract x type ...)
  (begin (dynamic-recursive-contract x '(type ...))
         (scv:ignore (c:recursive-contract x type ...))))
(define (dynamic-recursive-contract . _) (void))
