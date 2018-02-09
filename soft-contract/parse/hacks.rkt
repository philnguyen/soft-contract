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
         (prefix-in fake: "../fake-contract.rkt"))

(define-literal-set lits
  (let-values #%plain-lambda #%plain-app begin quote if #%variable-reference values list call-with-values))

(splicing-local
    ((define names '(call-with-input-file
                      call-with-output-file
                      open-input-file
                      open-output-file
                      file->list
                      file->value
                      with-input-from-file
                      with-output-to-file
                      string-join))
     (define (?recognized-name name)
       (define name-str (symbol->string name))
       (for/first ([s (in-list names)]
                   #:when (string-prefix? name-str (symbol->string s)))
         s)))
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
    ((define names {seteq 'make-sequence
                          'in-list
                          'in-range
                          'in-hash
                          'in-hash-keys
                          'in-hash-values
                          'in-set
                          'in-vector
                          'in-naturals
                          })
     (define aliases (hasheq 'default-in-hash 'in-hash
                             'default-in-hash-keys 'in-hash-keys
                             'default-in-hash-values 'in-hash-values
                             'real-set/c-name 'set/c))
     (define (?private-id-name id)
       (if (set-member? names id)
           id
           (hash-ref aliases id #f))))
  (define-syntax-class private-id
    #:description "hack pattern for some private identifiers"
    (pattern x:id
             #:attr name (?private-id-name (syntax-e #'x))
             #:when (attribute name))))


(define-syntax-class scv-provide
  #:description "hacked scv provide form"
  #:literal-sets (lits)
  (pattern (#%plain-app
            call-with-values
            (#%plain-lambda ()
                            (#%plain-app (~literal fake:dynamic-provide/contract) prov ...))
            _)
           #:attr provide-list #'(prov ...)))

(define-syntax-class scv-parametric->/c
  #:description "hacked parametric contract"
  #:literal-sets (lits)
  #:attributes (params body)
  (pattern (#%plain-app
            make-polymorphic-contract:id
            opaque/c:id
            _
            (#%plain-lambda (x:id ...) c)
            _)
           #:when (equal? (syntax-e #'make-polymorphic-contract) 'make-polymorphic-contract)
           #:when (equal? (syntax-e #'opaque/c) 'opaque/c)
           #:attr params #'(x ...)
           #:attr body #'c))

(define-syntax-class named-dom
  #:description "restricted fake-contract named domain"
  #:literal-sets (lits)
  #:attributes (name dependency body)
  (pattern (#%plain-app list (quote #f) (quote x:id) c:expr)
           #:attr name (syntax-e #'x)
           #:attr dependency #f
           #:attr body #'c)
  (pattern (#%plain-app list (quote #t) (quote x:id) (#%plain-lambda (z:id ...) c:expr))
           #:attr name (syntax-e #'x)
           #:attr dependency #'(z ...)
           #:attr body #'c))

(define-syntax-class scv-->i
  #:description "hacked dependent contract"
  #:literal-sets (lits)
  #:attributes (domains range)
  (pattern (~or (begin
                  (#%plain-app (~literal fake:dynamic->i) (#%plain-app list c:named-dom ...) d:named-dom)
                  _ ...)
                (let-values ()
                  (#%plain-app (~literal fake:dynamic->i) (#%plain-app list c:named-dom ...) d:named-dom)
                  _ ...)
                (#%plain-app (~literal fake:dynamic->i) (#%plain-app list c:named-dom ...) d:named-dom))
           #:attr domains (syntax->list #'(c ...))
           #:attr range #'d))

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

(define-syntax-class scv-->
  #:description "hacked non-dependent function contract"
  #:literal-sets (lits)
  #:attributes (inits ?rest range)
  (pattern (let-values ([(_) (~literal fake:dynamic->*)]
                        [(_) (#%plain-app list cs ...)]
                        [(_) rst]
                        [(_) rng])
             _ ...)
           #:attr inits (syntax->list #'(cs ...))
           #:attr ?rest #'rst
           #:attr range (range-expr #'rng))
  (pattern (let-values ([(_) (~literal fake:dynamic->*)]
                        [(_) (#%plain-app list cs ...)]
                        [(_) rng])
             _ ...)
           #:attr inits (syntax->list #'(cs ...))
           #:attr ?rest #f
           #:attr range (range-expr #'rng)))

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
           #:attr ref (syntax-e #'x)))

(define-syntax-class scv-struct/c
  #:description "scv hacked struct/c"
  #:literal-sets (lits)
  #:attributes (name fields)
  (pattern (begin (#%plain-app (~literal fake:dynamic-struct/c) _ c ...)
                  (#%plain-app _ _ _ _ (quote k) _ ...)
                  _ ...)
           #:attr name (syntax-e #'k)
           #:attr fields (syntax->list #'(c ...))))

(define-syntax-class scv-struct-out
  #:description "hacked scv struct-out"
  #:literal-sets (lits)
  #:attributes (name field-names field-contracts loc)
  (pattern (#%plain-app (~literal fake:dynamic-struct-out)
                        (quote s:id)
                        (#%plain-app list (quote ac:id) c) ...)
           #:attr loc (syntax-ℓ #'s)
           #:attr name (syntax-e #'s)
           #:attr field-names (map syntax-e (syntax->list #'(ac ...)))
           #:attr field-contracts (syntax->list #'(c ...))))

(define range-expr
  (syntax-parser
    #:literal-sets (lits)
    [(#%plain-app list d) #'d]
    [_ 'any]))
