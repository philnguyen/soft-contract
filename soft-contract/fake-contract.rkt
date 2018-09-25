#lang racket/base

(require (except-in racket/contract
                    flat-contract
                    -> ->i case-> and/c or/c any/c none/c list/c listof struct/c ->* provide/contract
                    one-of/c =/c >/c >=/c </c <=/c between/c not/c cons/c box/c vector/c vectorof hash/c
                    parametric->/c
                    recursive-contract
                    define/contract
                    contract?)
         (except-in racket/set set/c)
         (for-syntax racket/base
                     racket/string
                     racket/syntax
                     syntax/parse)
         racket/list
         syntax/parse/define)
(require (prefix-in c: racket/contract/base)
         (prefix-in c: (only-in racket/set set/c))
         (prefix-in r: racket/base))

(provide (all-from-out racket/contract/base) provide
         flat-contract
         -> ->i case-> and/c or/c any/c none/c list/c listof struct/c ->* provide/contract contract-out false/c hash/c set/c
         parametric->/c
         recursive-contract
         (rename-out [c:any any])
         dynamic-provide/contract
         dynamic->i dynamic-> dynamic->* dynamic-case-> dynamic-parametric->/c
         dynamic-struct/c
         dynamic-recursive-contract
         dynamic-struct-out
         =/c >/c >=/c </c <=/c between/c
         not/c cons/c
         one-of/c box/c vector/c vectorof
         define/contract dynamic-mon
         contract?
         --> forall
         (rename-out [--> ⇒] [forall ∀]))

(define-syntax (scv:ignore stx)
  (syntax-case stx ()
    [(_ s) (syntax-property #'s 'scv:ignore #t)]))

(begin-for-syntax
  (define (with-syntax-source src stx)
    (datum->syntax src
                   (syntax-e stx)
                   (list (syntax-source src)
                         (syntax-line src)
                         (syntax-column src)
                         (syntax-position src)
                         (syntax-span src)))))

(define contract? c:contract?)
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
(define hash/c c:hash/c)
(define set/c c:set/c)
(define-syntax (struct/c stx) 
  (syntax-case stx ()
    [(_ name cs ...)
     #`(begin (dynamic-struct/c name cs ...)
              (scv:ignore (c:struct/c name cs ...)))]))
#;(define (dynamic->* #:mandatory-domain-contracts inits
                    #:rest-contract [rest-c #f]
                    #:range-contracts rng
                    #:total? [total? #f])
  (c:dynamic->* #:mandatory-domain-contracts inits
                #:rest-contract rest-c
                #:range-contracts rng))
(define-syntax-rule (parametric->/c (x ...) c) (dynamic-parametric->/c (λ (x ...) c)))

(begin-for-syntax
  (define-syntax-class dom
    #:description "restricted contract domain"
    (pattern (_:id (_:id ...) _:expr))
    (pattern (_:id            _:expr))))

(define-syntax dom-quote
  (syntax-parser
    [(_ (~and stx (name:id (dep:id ...) ctc:expr)))
     (with-syntax-source #'stx
       #'(list #t 'name (λ (dep ...) ctc)))]
    [(_ (~and stx (name:id              ctc:expr)))
     (with-syntax-source #'stx
       #'(list #f 'name              ctc ))]))

(define-syntax ->i
  (syntax-parser
    [(~and stx (_ (c:dom ...) d:dom (~optional (~seq #:total? total?:boolean)
                                               #:defaults ([total? #'#f]))))
     (with-syntax-source #'stx
       #'(begin
           (dynamic->i (list (dom-quote c) ...) (dom-quote d) total?)
           (scv:ignore (c:->i (c ...) d))))]))

(define (dynamic->i . _) (void))
(define (dynamic-> . _) (void))
(define (dynamic->* . _) (void))
(define (dynamic-struct/c . _) (void))
(define (dynamic-struct-out . _) (void))
(define (dynamic-parametric->/c v) v) 

(define-syntax ->
  (syntax-parser
    [(~and stx (-> cs:expr ... result-c:expr (~optional (~seq #:total? total?:boolean)
                                                        #:defaults ([total? #''#f]))))
     (with-syntax ([rng (syntax-parse #'result-c
                          [(~literal c:any) #'#f]
                          [_ #'(list result-c)])])
       (with-syntax-source #'stx
         #'(begin
             (dynamic-> (list cs ...) rng total?)
             (scv:ignore (c:-> cs ... result-c)))))]))
(define-syntax ->*
  (syntax-parser
    [(~and stx (->* (cs:expr ...) #:rest rest-c:expr result-c:expr
                    (~optional (~seq #:total? total?:boolean)
                               #:defaults ([total? #'#f]))))
     (with-syntax ([rng (syntax-parse #'result-c
                          [(~literal c:any) #'#f]
                          [_ #'(list result-c)])])
       (with-syntax-source #'stx
         #'(begin
             (dynamic->* (list cs ...) rest-c rng total?)
             (c:->* (cs ...) #:rest rest-c result-c))))]))

(define-syntax case->
  (syntax-parser
    [(~and stx (_ clauses ...))
     (with-syntax-source #'stx
       #'(begin
           (case->/acc () (clauses ...))
           ;; TODO can't enable below yet, because hacky expansion replaces `->` and `->*`
           #;(scv:ignore (c:case-> clauses ...))))]))

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

(require (for-syntax syntax/parse))

(define-syntax (provide stx)
  (syntax-parse stx #:literals (contract-out struct struct-out)
    [(_ (~or i:id
             (struct-out so:id)
             (contract-out (~or [p/i:id ctc:expr]
                                [struct s:id ([ac:id dom:expr] ...)]) ...))
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

(define-syntax define/contract
  (syntax-rules ()
    [(_ (f x ...) c e ...) (define f (dynamic-mon 'f c (λ (x ...) e ...)))]
    [(_ x         c e    ) (define x (dynamic-mon 'x c e))]))

(define (dynamic-mon x c e) e)

;; Phil's clueless hack for `recursive-contract`
(define-syntax-rule (recursive-contract x type ...)
  (begin (dynamic-recursive-contract x '(type ...))
         (scv:ignore (c:recursive-contract x type ...))))
(define (dynamic-recursive-contract . _) (void))

;; Syntactic sugar for theorem proving
(define-simple-macro
  (--> ([x:id c] ...) d)
  (->i ([x c] ...) (res (x ...) (λ _ d)) #:total? #t))
(define-simple-macro
  (forall (α:id ...) e)
  (c:parametric->/c (α ...) e))
