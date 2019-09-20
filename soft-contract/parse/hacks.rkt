#lang racket/base

(provide (all-defined-out))

(require racket/set
         racket/match
         racket/list
         racket/splicing
         racket/string
         racket/syntax
         syntax/parse
         "../ast/srcloc.rkt"
         "../ast/signatures.rkt"
         (prefix-in fake: "../fake-contract.rkt")
         (prefix-in r5: r5rs))

(define-literal-set lits
  (let-values #%plain-lambda #%plain-app begin quote if #%variable-reference values list call-with-values
   define-syntaxes quote-syntax lambda))

(define (first-prefix ids s)
  (define s:str (symbol->string s))
  (for/or ([id (in-list ids)] #:when (string-prefix? s:str (symbol->string id)))
    id))

(splicing-local
    ((define names '(call-with-input-file
                      call-with-output-file
                      open-input-file
                      open-output-file
                      file->list
                      file->value
                      file->lines
                      with-input-from-file
                      with-output-to-file
                      string-join
                      sort
                      remove-duplicates
                      string-trim
                      sequence/c
                      string-split))
     (define (?recognized-name name) (first-prefix names name)))
  (define-syntax-class indirect-app
    #:description "hack pattern for some `variable-reference-constant?` usages"
    #:literal-sets (lits)
    (pattern (if (#%plain-app (~literal variable-reference-constant?)
                              (#%variable-reference f:id))
                 (#%plain-app g*:id _ ...)
                 (#%plain-app g:id x ...))
             #:attr fun-name (?recognized-name (syntax-e #'g))
             #:when (free-identifier=? #'f #'g)
             #:when (attribute fun-name)
             #:attr args #'(x ...))))

(splicing-local
    ((define names '(make-sequence
                     in-list
                     in-range
                     in-hash
                     in-hash-keys
                     in-hash-values
                     in-set
                     in-vector
                     in-naturals
                     call-with-input-file
                     call-with-output-file
                     open-input-file
                     open-output-file))
     (define aliases (hasheq 'default-in-hash 'in-hash
                             'default-in-hash-keys 'in-hash-keys
                             'default-in-hash-values 'in-hash-values
                             'real-set/c-name 'set/c
                             'new-apply-proc 'apply))
     (define (?private-id-name id)
       (or (hash-ref aliases id #f) (first-prefix names id))))
  (define-syntax-class private-id
    #:description "hack pattern for some private identifiers"
    (pattern x:id
             #:attr name (?private-id-name (syntax-e #'x))
             #:when (attribute name))))

(define-syntax-class scv-ignored
  #:description "non-sense ignored by scv"
  #:literal-sets (lits)
  (pattern (if (#%plain-app (~literal variable-reference-from-unsafe?)
                            (#%variable-reference))
               (#%plain-app void)
               (let-values () (#%plain-app check-list _ ...)))))


(define-syntax-class scv-provide
  #:description "hacked scv provide form"
  #:literal-sets (lits)
  (pattern (#%plain-app
            call-with-values
            (#%plain-lambda ()
                            (#%plain-app (~literal fake:dynamic-provide/contract) prov ...))
            _)
           #:attr provide-list #'(prov ...)))

(define-syntax-class scv-define-opaque
  #:description "hacked scv define opaque form"
  #:literal-sets (lits)
  (pattern (#%plain-app
            call-with-values
            (#%plain-lambda () (#%plain-app (~literal fake:dynamic-define-opaque) x:id))
            _)
           #:attr name #'x))

(define-syntax-class scv-parametric->/c
  #:description "hacked parametric contract"
  #:literal-sets (lits)
  #:attributes (params body)
  (pattern (#%plain-app
            make-polymorphic-contract:id
            opaque/c:id
            _
            (#%plain-lambda (x:id ...) c ...)
            _)
           #:when (equal? (syntax-e #'make-polymorphic-contract) 'make-polymorphic-contract)
           #:when (equal? (syntax-e #'opaque/c) 'opaque/c)
           #:attr params #'(x ...)
           #:attr body #'(begin c ...))
  (pattern (#%plain-app (~literal fake:dynamic-parametric->/c) (#%plain-lambda (x:id ...) c:expr ...))
           #:attr params #'(x ...)
           #:attr body #'(begin c ...)))

(define-syntax-class named-dom
  #:description "restricted dependent named domain"
  #:literal-sets (lits)
  #:attributes (name dependency body)
  (pattern (#%plain-app list (quote #f) (quote x:id) c:expr)
           #:attr name #'x
           #:attr dependency #f
           #:attr body #'c)
  (pattern (#%plain-app list (quote #t) (quote x:id) (#%plain-lambda (z:id ...) c:expr ...))
           #:attr name #'x
           #:attr dependency (syntax->list #'(z ...))
           #:attr body #'(begin c ...)))

(define-syntax-class scv-->i
  #:description "hacked dependent contract"
  #:literal-sets (lits)
  #:attributes (init-domains rest-domain ranges total?)
  (pattern (~or (begin
                  (#%plain-app (~literal fake:dynamic->i)
                               (#%plain-app list c:named-dom ...)
                               (~and cr (~or (quote #f) _:named-dom))
                               (~and ds (~or (quote #f) (#%plain-app list d:named-dom ...)))
                               (quote tot?:boolean))
                  _ ...)
                (let-values ()
                  (#%plain-app (~literal fake:dynamic->i)
                               (#%plain-app list c:named-dom ...)
                               (~and cr (~or (quote #f) _:named-dom))
                               (~and ds (~or (quote #f) (#%plain-app list d:named-dom ...)))
                               (quote tot?:boolean))
                  _ ...)
                (#%plain-app (~literal fake:dynamic->i)
                               (#%plain-app list c:named-dom ...)
                               (~and cr (~or (quote #f) _:named-dom))
                               (~and ds (~or (quote #f) (#%plain-app list d:named-dom ...)))
                               (quote tot?:boolean)))
           #:attr init-domains (syntax->list #'(c ...))
           #:attr rest-domain (syntax-parse #'cr
                                [(quote #f) #f]
                                [_ #'cr])
           #:attr ranges (syntax-parse #'ds
                           #:literal-sets (lits)
                           [(quote #f) #f]
                           [(#%plain-app list d ...) (syntax->list #'(d ...))])
           #:attr total? (syntax-e #'tot?)))

(define-syntax-class scv-case->
  #:description "hacked case contract"
  #:literal-sets (lits)
  #:attributes (cases)
  (pattern (~or (begin
                  (#%plain-app
                   (~literal fake:dynamic-case->)
                   (~and kase (#%plain-app list (#%plain-app list inits ...) rests rng)) ...))
                (let-values ()
                  (#%plain-app
                   (~literal fake:dynamic-case->)
                   (~and kase (#%plain-app list (#%plain-app list inits ...) rests rng)) ...))
                (#%plain-app
                 (~literal fake:dynamic-case->)
                 (~and kase (#%plain-app list (#%plain-app list inits ...) rests rng)) ...))
           #:attr cases (map
                         (syntax-parser
                           #:literal-sets (lits)
                           [(~and stx (#%plain-app list (#%plain-app list inits ...) rest rng))
                            (list (syntax->list #'(inits ...))
                                  (syntax-parse #'rest
                                    ['#f #f]
                                    [_ #'rest])
                                  (range-expr #'rng)
                                  #'stx)])
                         (syntax->list #'(kase ...)))))

(define-syntax-class scv-fake-lit
  #:description "fake literals"
  #:attributes (real)
  (pattern (~literal fake:any/c) #:attr real 'any/c)
  (pattern (~literal fake:none/c) #:attr real 'none/c)
  (pattern (~literal fake:not/c) #:attr real 'not/c)
  (pattern (~literal fake:and/c) #:attr real 'and/c)
  (pattern (~literal fake:or/c ) #:attr real 'or/c)
  (pattern (~literal fake:false/c) #:attr real 'not)
  (pattern (~literal fake:listof) #:attr real 'listof)
  (pattern (~literal fake:list/c) #:attr real 'list/c)
  (pattern (~literal fake:between/c) #:attr real 'between/c)
  (pattern (~literal fake:flat-contract) #:attr real 'values)
  (pattern (~literal fake:hash/c) #:attr real 'hash/c) ; TODO doesn't work
  (pattern (~literal fake:set/c) #:attr real 'set/c)
  (pattern (~literal fake:dynamic-mon) #:attr real 'scv:mon)
  (pattern (~literal fake:contract?) #:attr real 'contract?)

  ;; FIX Tmp. Hacks for Scheme programs
  (pattern (~literal r5:pair?) #:attr real -cons?)
  (pattern (~literal r5:cdr) #:attr real -cdr)
  (pattern (~literal r5:car) #:attr real -car)
  (pattern (~literal r5:cons) #:attr real -cons)
  (pattern (~literal r5:set-car!) #:attr real -set-car!)
  (pattern (~literal r5:set-cdr!) #:attr real -set-cdr!)
  (pattern (~literal r5:memq) #:attr real 'memq)
  (pattern (~literal r5:list->mlist) #:attr real 'list)
  (pattern (~literal r5:vector->list) #:attr real 'vector->list)
  (pattern (~literal r5:list->vector) #:attr real 'list->vector)
  (pattern (~literal r5:display) #:attr real 'display)
  (pattern (~literal r5:length) #:attr real 'length)
  (pattern (~literal r5:assq) #:attr real 'assq)
  (pattern (~literal r5:map) #:attr real 'map)
  (pattern (~literal r5:caddr) #:attr real 'caddr)
  (pattern (~literal r5:caaaar) #:attr real 'caaaar)
  (pattern (~literal r5:append) #:attr real 'append))

(define-syntax-class scv-fake-cmp
  #:description "fake comparison contract combinator"
  #:attributes (op)
  (pattern (~literal fake:=/c ) #:attr op '= )
  (pattern (~literal fake:>/c ) #:attr op '> )
  (pattern (~literal fake:>=/c) #:attr op '>=)
  (pattern (~literal fake:</c ) #:attr op '< )
  (pattern (~literal fake:<=/c) #:attr op '<=))


(define-syntax-class scv-struct-decl
  #:description "struct declaration"
  #:literal-sets (lits)
  #:attributes (constructor-name extra-constructor-name ?parent predicate-name
                field-count accessors+mutators
                )
  (pattern (define-values (type:id _ pred acc+muts ...)
             (let-values ([(_ ...)
                           (let-values ()
                             (let-values ()
                               (#%plain-app (~literal make-struct-type)
                                            (quote ctor-name)
                                            parent
                                            (quote n:exact-integer)
                                            _ ...)))])
               (#%plain-app values _ _ _ mk-acc+muts ...)))
           #:attr constructor-name (syntax-e #'ctor-name)
           #:attr predicate-name (syntax-e #'pred)
           #:attr field-count (syntax-e #'n)
           #:attr extra-constructor-name #'type
           #:attr ?parent (syntax-parse #'parent
                            ['#f #f]
                            [p:id #'p])
           #:attr
           accessors+mutators
           (call-with-values
            (λ ()
              (for/fold ([accs (hasheq)]
                         [muts (hasheq)])
                        ([name (in-list (syntax->list #'(acc+muts ...)))]
                         [expr (in-list (syntax->list #'(mk-acc+muts ...)))])
                (define/syntax-parse (#%plain-app mk _ (quote i:exact-integer) _) expr)
                (syntax-parse #'mk
                  [(~literal make-struct-field-accessor)
                   (values (hash-set accs (syntax-e #'i) (syntax-e name)) muts)]
                  [(~literal make-struct-field-mutator)
                   (values accs (hash-set muts (syntax-e #'i) (syntax-e name)))])))
            cons)))

(define-syntax-class scv-x/c
  #:description "scv restricted recursive contract reference"
  #:attributes (ref)
  #:literal-sets (lits)
  (pattern (~or (let-values ()
                  (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)) _ ...)
                (begin (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)) _ ...)
                (#%plain-app (~literal fake:dynamic-recursive-contract) x:id (quote t)))
           #:when (syntax-parse #'t
                    [((~or #:chaperone #:flat)) #t]
                    [_
                     (raise-syntax-error 'recursive-contract "must be #:chaperone or #:flat" #'t)])
           #:attr ref #'x))

(define-syntax-class scv-struct/c
  #:description "scv hacked struct/c"
  #:literal-sets (lits)
  #:attributes (name fields)
  (pattern (begin (#%plain-app (~literal fake:dynamic-struct/c) tag c ...)
                  _ ...)
           #:attr name #'tag
           #:attr fields (syntax->list #'(c ...))))

(define-syntax-class scv-struct-out
  #:description "hacked scv struct-out"
  #:literal-sets (lits)
  #:attributes (struct-id field-names field-contracts loc)
  (pattern (#%plain-app (~literal fake:dynamic-struct-out)
                        (quote s:id)
                        (#%plain-app list (quote ac:id) c) ...)
           #:attr loc (syntax-ℓ #'s)
           #:attr struct-id #'s
           #:attr field-names (map syntax-e (syntax->list #'(ac ...)))
           #:attr field-contracts (syntax->list #'(c ...))))

(define-syntax-class scv-id-struct-out
  #:description "hacked scv id-struct-out"
  #:literal-sets (lits)
  #:attributes (struct-id)
  (pattern (#%plain-app (~literal fake:dynamic-id-struct-out) (quote s:id))
           #:attr struct-id #'s))

(define-syntax-class scv-struct-info-alias
  #:description "struct info alias pattern"
  #:literal-sets (lits)
  #:attributes (lhs rhs)
  ;; FIXME for some reason, matching against literals `#%plain-app` and `#%plain-lambda` won't work
  (pattern (define-syntaxes
             (x:id)
             (_#%plain-app1
              f:id
              (_#%plain-lambda1 ()
                (_#%plain-app2
                 _list1
                 (quote-syntax _:id)
                 (quote-syntax z:id)
                 (quote-syntax _:id)
                 (_#%plain-app3 _list2 _ ...)
                 (_#%plain-app4 _list3 _ ...)
                 _))
              (_#%plain-lambda2 () (quote-syntax v:id))
              (_#%plain-lambda3 () (quote-syntax _:id))))
           #:when (equal? (syntax-e #'f) 'make-applicable-contract-out-redirect-struct-info)
           #:when (equal? (syntax-e #'x) (syntax-e #'z))
           #:attr lhs (syntax-e #'x)
           #:attr rhs #'v))

(define range-expr
  (syntax-parser
    #:literal-sets (lits)
    [(#%plain-app list d) #'d]
    [_ 'any]))
