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
                     syntax/parse
                     racket/pretty
                     "parse/utils.rkt")
         racket/list
         racket/splicing
         syntax/parse/define
         (prefix-in c: racket/contract/base)
         (prefix-in c: (only-in racket/set set/c))
         (prefix-in r: racket/base))

(provide (all-from-out racket/contract/base) provide
         -> ->* ->i case-> struct/c provide/contract contract-out
         parametric->/c
         recursive-contract
         (rename-out [c:any any])
         dynamic-provide/contract
         dynamic->i dynamic-case-> dynamic-parametric->/c
         dynamic-struct/c
         dynamic-recursive-contract
         dynamic-struct-out
         dynamic-id-struct-out
         define/contract dynamic-mon
         --> forall
         (rename-out [--> ⇒] [forall ∀]))

(define-syntax (scv:ignore stx)
  (syntax-case stx ()
    [(_ s) (syntax-property #'s 'scv:ignore #t)])) 

(define-syntax (struct/c stx) 
  (syntax-case stx ()
    [(_ name cs ...)
     (with-syntax-source stx
       #'(begin (dynamic-struct/c name cs ...)
                (scv:ignore (c:struct/c name cs ...))))]))

(define-syntax-rule (parametric->/c (x ...) c) (dynamic-parametric->/c (λ (x ...) c)))

(begin-for-syntax 
  (define-syntax-class dom
    #:description "restricted dependent domain"
    (pattern _:id+ctc))
  (define-syntax-class rng
    #:description "restricted dependent range"
    (pattern (~literal any))
    (pattern _:id+ctc)
    (pattern _:un+ctc)
    (pattern ((~literal values) _:id+ctc ...))
    (pattern ((~literal values) _:un+ctc ...)))
  (define-syntax-class id+ctc
    #:description "named contract domain"
    (pattern (_:id (_:id ...) _:expr))
    (pattern (_:id            _:expr)))
  (define-syntax-class un+ctc
    #:description "unnamed contract domain"
    (pattern [(~literal _) _:expr])
    (pattern [(~literal _) (_:id ...) _:expr])))

(splicing-local
    ((define-syntax re-export
       (syntax-parser
         [(_ x ...)
          (with-syntax ([(c:x ...)
                         (for/list ([x (in-list (syntax->list #'(x ...)))])
                           (format-id x "c:~a" x))])
            #'(begin (define x c:x) ...
                     (provide x ...)))])))
  (re-export hash/c set/c contract? flat-contract
             listof list/c cons/c box/c vector/c vectorof
             any/c none/c and/c or/c one-of/c not/c false/c
             =/c </c <=/c >/c >=/c between/c))

(define-syntax dom-quote
  (let ([gen-name (syntax-parser
                    [(~literal _) (generate-temporary '_)]
                    [x #'x])])
    (syntax-parser
      [(_ (~and stx (name (dep:id ...) ctc:expr)))
       (with-syntax ([name* (gen-name #'name)])
         (with-syntax-source #'stx
           ;; not explicitly using `#%plain-app` here results in ambiguous identifier error
           ;; TODO: find proper fix
           #'(#%plain-app list #t 'name* (λ (dep ...) ctc))))]
      [(_ (~and stx (name              ctc:expr)))
       (with-syntax ([name* (gen-name #'name)])
         (with-syntax-source #'stx
           ;; not explicitly using `#%plain-app` here results in ambiguous identifier error
           ;; TODO: find proper fix
           #'(#%plain-app list #f 'name*              ctc )))])))

(define-syntax ->i
  (syntax-parser
    [(~and stx
           (_ (c:dom ...)
              (~optional (~seq #:rest rest:id+ctc)
                         #:defaults ([rest #'#f]))
              d:rng
              (~optional (~seq #:total? total?:boolean)
                         #:defaults ([total? #'#f]))))
     (with-syntax-source #'stx
       #`(begin
           (dynamic->i (list (dom-quote c) ...)
                       #,(if (syntax-e #'rest) #'(dom-quote rest) #'#f)
                       #,(syntax-parse #'d
                           [(~literal c:any) #'#f]
                           [((~literal values) d ...) #'(list (dom-quote d) ...)]
                           [d #'(list (dom-quote d))])
                       total?)
           (scv:ignore (c:->i (c ...) d))))]))

(define-syntaxes (-> ->*)
  (let ([gen-dom
         (λ (c)
           (with-syntax ([x (generate-temporary '_)])
             (with-syntax-source c #`(x #,c))))]
        [gen-range-dom
         (syntax-parser
           [(~literal c:any) #'c:any]
           [(~and r ((~literal values) d ...))
            #`(values #,@(for/list ([dᵢ (in-list (syntax->list #'(d ...)))])
                          (with-syntax-source dᵢ #`(_ #,dᵢ))))]
           [d (with-syntax-source #'d #'(_ d))])])
    (values
     (syntax-parser
       [(~and stx (-> cs:expr ... result-c:expr (~optional (~seq #:total? total?:boolean)
                                                           #:defaults ([total? #'#f]))))
        (with-syntax ([(dom ...) (map gen-dom (syntax->list #'(cs ...)))]
                      [rng (gen-range-dom #'result-c)])
          (with-syntax-source #'stx
            #'(->i (dom ...) rng #:total? total?)))])
     (syntax-parser
       [(~and stx (->* (cs:expr ...) #:rest rest-c:expr result-c:expr
                       (~optional (~seq #:total? total?:boolean)
                                  #:defaults ([total? #'#f]))))
        (with-syntax ([(dom-init ...) (map gen-dom (syntax->list #'(cs ...)))]
                      [dom-rest  (gen-dom #'rest-c)]
                      [rng (gen-range-dom #'result-c)])
          (with-syntax-source #'stx
            #'(->i (dom-init ...) #:rest dom-rest rng #:total? total?)))]))))

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

(define-syntax-rule (provide/contract [id ctc] ...)
  (begin (dynamic-provide/contract (list id ctc) ...)
         (scv:ignore (c:provide/contract [id ctc] ...)))) 

(define-syntax (provide stx)
  (syntax-parse stx #:literals (contract-out struct struct-out)
    [(_ (~or i:id
             (struct-out so:id)
             (contract-out (~or [p/i:id ctc:expr]
                                ;; TODO confirm that ignoring parent declaration makes no difference
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
          (dynamic-id-struct-out 'so) ...
          (dynamic-struct-out 's (list 'ac dom) ...) ... ...))]))

(define-syntax define/contract
  (syntax-parser
    [(_ (f x ...) c e ...)
     (with-syntax ([rhs (with-syntax-source #'(f x ...)
                          #'(dynamic-mon 'f c (λ (x ...) e ...)))])
       #'(define f rhs))]
    [(_ x         c e    )
     (with-syntax ([rhs (with-syntax-source #'x #'(dynamic-mon 'x c e))])
       #'(define x rhs))]))

(define (dynamic-mon x c e) e)

;; Phil's clueless hack for `recursive-contract`
(define-syntax-rule (recursive-contract x type ...)
  (begin (dynamic-recursive-contract x '(type ...))
         (scv:ignore (c:recursive-contract x type ...))))

;; Dummy stuff
(define (dynamic->i . _) (void))
(define (dynamic-struct/c . _) (void))
(define (dynamic-struct-out . _) (void))
(define (dynamic-id-struct-out _) (void))
(define (dynamic-parametric->/c v) v)
(define (dynamic-case-> . _) (void))
(define (dynamic-provide/contract . _) (void))
(define (dynamic-recursive-contract . _) (void))

;; Syntactic sugar for theorem proving
(define-simple-macro
  (--> ([x:id c] ...) d)
  (->i ([x c] ...) (res (x ...) (λ _ d)) #:total? #t))
(define-simple-macro
  (forall (α:id ...) e)
  (c:parametric->/c (α ...) e))
