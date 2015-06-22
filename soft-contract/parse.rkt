#lang racket/base
(require racket/match racket/list racket/set racket/bool racket/function racket/math
         racket/unsafe/ops
         web-server/private/util
         "utils.rkt" "lang.rkt" (only-in redex/reduction-semantics variable-not-in)
         syntax/parse syntax/modresolve racket/pretty racket/contract
         "expand.rkt"
         (prefix-in fake: "fake-contract.rkt"))
(provide (all-defined-out) #;read-p #;on-•!)

(define (dummy)
  (log-warning "Misreading syntax, returning dummy expression")
  (.b 'FIXME-dummy-data))

(define/contract (files->prog paths)
  ((listof path-string?) . -> . .prog?)
  (define/contract ms (listof .module?)
    (for/list ([path (in-list paths)])
      (parse-top-level-form (do-expand-file path))))
  (define-values (havoc-m havoc-e) (gen-havoc ms))
  (.prog (cons havoc-m ms) havoc-e))

;; TODO For testing only
(define ids (box '()))

(define/contract cur-mod (parameter/c string? #|TODO|#)
  (make-parameter "top-level"))

(define scv-syntax? (and/c syntax? (not/c scv-ignore?)))
(define env? (listof identifier?))

;; Read our current limited notion of program
(define/contract (parse-prog mods top)
  ((listof scv-syntax?) scv-syntax? . -> . .prog?)
  (.prog (parse-mods mods) (parse-expr top)))

(define/contract (parse-mods mods)
  ((listof scv-syntax?) . -> . (listof .module?))
  (todo 'parse-mods))

(define (mod-path->mod-name p)
  (match p ; hacks
    ['#%kernel 'Λ]
    ['#%unsafe 'unsafe]
    [(and (? symbol?) (app symbol->string "expanded module")) (cur-mod)]
    [_ (path->string (simplify-path p))]))

(define/contract (parse-top-level-form form)
  (scv-syntax? . -> . .top-level-form?)
  (log-debug "parse-top-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path (#%plain-module-begin forms ...))
     (define mod-name (mod-path->mod-name (syntax-source #'id)))
     (.module
      mod-name
      (parameterize ([cur-mod mod-name])
        (.plain-module-begin
         (filter
          values
          (for/list ([formᵢ (in-list (syntax->list #'(forms ...)))]
                     #:when
                     (syntax-parse formᵢ
                       [((~literal module) (~literal configure-runtime) _ ...) #f]
                       [_ #t])
                     #:when
                     (scv-syntax? formᵢ))
            (parse-module-level-form formᵢ))))))]
    [((~literal begin) form ...)
     (-begin (map parse-top-level-form (syntax->list #'(form ...))))]
    [((~literal #%expression) e) (parse-expr #'e)]
    [_ (parse-general-top-level-form form)]))

(define/contract (parse-module-level-form form)
  (scv-syntax? . -> . (or/c #f .module-level-form?))
  (log-debug "parse-module-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                call-with-values)
    [(#%provide spec ...)
     (.provide (map parse-provide-spec (syntax->list #'(spec ...))))]
    [(#%declare _ ...) (todo '#%declare)]
    [(begin-for-syntax _ ...) #|ignore|# #f]
    
    ;; Hack for reading our fake-contracts:
    [(#%plain-app
      call-with-values
      (#%plain-lambda
       ()
       (#%plain-app
        (~literal fake:dynamic-provide/contract)
        (#%plain-app (~literal list) x:id c:expr) ...))
      _)
     #;(debug "x: ~a~nc: ~a~n"
             (identifier? (car (syntax->list #'(x ...))))
             (identifier? (car (syntax->list #'(c ...)))))
     (.provide (for/list ([x (in-list (syntax->list #'(x ...)))]
                          [c (in-list (syntax->list #'(c ...)))])
                 (.p/c-item (syntax-e x) (parse-expr c))))]
    
    [_ (or (parse-general-top-level-form form)
           (parse-submodule-form form))]))

(define/contract (parse-submodule-form form)
  (scv-syntax? . -> . (or/c #f .submodule-form?))
  (log-debug "parse-submodule-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path ((~literal #%plain-module-begin) d ...))
     (.module
      (path->string (simplify-path (syntax-source #'id)))
      (.plain-module-begin (map parse-module-level-form (syntax->list #'(d ...)))))]
    [((~literal module*) _ ...) (todo 'module*)]
    [_ #f]))

(define/contract (parse-general-top-level-form form)
  (scv-syntax? . -> . (or/c #f .general-top-level-form?))
  (log-debug "parse-general-top-level-form:~n~a~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (define-syntaxes define-values #%require let-values #%plain-app values
                 call-with-values)
    [(define-values (_ ctor pred acc ...)
       (let-values ([(_ ...)
                     (let-values ()
                       (let-values ()
                         (#%plain-app _ ctor-name _ ...)))])
         (#%plain-app values _ _ _ (#%plain-app _ _ _ _) ...)))
     ;(define/contract ctor-name symbol? (syntax-e #'ctor-name))
     (define/contract ctor-name symbol? (syntax-e #'ctor))
     (define/contract accs (listof identifier?) (syntax->list #'(acc ...)))
     (define n (length accs))
     (.define-values
      (list* ctor-name (syntax-e #'pred) (map syntax-e accs))
      (.@ 'values
          (list* (.st-mk (.id ctor-name (cur-mod)) n)
                 (.st-p (.id ctor-name (cur-mod)) n)
                 (for/list ([accᵢ (in-list accs)] [i (in-naturals)])
                   (.st-ac (.id ctor-name (cur-mod)) n i)))
          'Λ))]
    [(define-values (x:identifier) e) ; FIXME: separate case hack to "close" recursive contract
     (define lhs (syntax-e #'x))
     (define rhs (parse-expr #'e))
     (define frees (free-x/c rhs))
     (cond
       [(set-empty? frees) (.define-values (list lhs) rhs)]
       [(set-empty? (-- frees lhs)) (.define-values (list lhs) (.μ/c lhs rhs))]
       [else
        (error 'TODO
               "In ~a's definition: arbitrary reference (recursive-contract ~a) not supported for now."
               lhs (set-first (-- frees lhs)))])]
    [(define-values (x:identifier ...) e)
     (.define-values (map syntax-e (syntax->list #'(x ...))) (parse-expr #'e))]
    [(#%require spec ...)
     (.require (map parse-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes _ ...) #f] 
    [_ (parse-expr form)]))

(define dummy-id #'dummy)

(define/contract (parse-expr stx [ctx '()])
  (scv-syntax? . -> . .expr?)
  (log-debug "parse-expr: ~a~n~n" (pretty-format (syntax->datum stx)))

  (define/contract (go e)
    (scv-syntax? . -> . .expr?)
    (parse-expr e ctx))

  (define/contract (go/list es)
    ((and/c scv-syntax? (not/c identifier?)) . -> . (listof .expr?))
    (map go (syntax->list es)))
  
  (syntax-parse stx
    #:literals
    (let-values letrec-values begin begin0 if #%plain-lambda #%top
                module* module #%plain-app quote #%require quote-syntax
                with-continuation-mark #%declare #%provide case-lambda
                #%variable-reference set! list)
    ;;; Contracts
    ;; Non-dependent function contract
    [(let-values ([(_) #|TODO|# _]
                  [(_) (#%plain-app list c ...)]
                  [(_) (#%plain-app list d)])
       _ ...)
     (.->i (go/list #'(c ...))
           (parse-expr #'d (ext-env ctx (make-list (length (syntax->list #'(c ...))) dummy-id)))
           #f)
     #;(.-> (map parse-expr (syntax->list #'(c ...)))
          (parse-expr #'d))]
    ;; Dependent contract
    [(begin
       (#%plain-app
        (~literal fake:dynamic->i)
        (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
        (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
       _ ...)
     ;(printf "dynamic->id₁: ~a~n" (syntax->datum #'d))
     (define xs (syntax->list #'(z ...)))
     (define ctx′ (ext-env ctx xs))
     (.->i (go/list #'(cₓ ...)) (parse-expr #'d ctx′) #f)]
    ; FIXME: duplicate of above case, (let-values () e _ ...) == (begin () e _ ...)
    [(let-values ()
       (#%plain-app
        (~literal fake:dynamic->i)
        (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
        (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
       _ ...)
     ;(printf "dynamic->id₁: ~a~n" (syntax->datum #'d))
     (define xs (syntax->list #'(z ...)))
     (define ctx′ (ext-env ctx xs))
     (.->i (go/list #'(cₓ ...)) (parse-expr #'d ctx′) #f)]
    ; FIXME: duplicate of above case, (begin e _ ...) == e
    [(#%plain-app
      (~literal fake:dynamic->i)
      (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
      (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
     ;(printf "dynamic->id₂: ~a~n" (syntax->datum #'d))
     (define xs (syntax->list #'(z ...)))
     (define ctx′ (ext-env ctx xs))
     (.->i (go/list #'(cₓ ...)) (parse-expr #'d ctx′) #f)]
    ;; Conjunction
    [(#%plain-app (~literal fake:and/c) c ...)
     (apply .and/c (go/list #'(c ...)))]
    ;; Disjunction
    [(#%plain-app (~literal fake:or/c) c ...)
     (apply .or/c (go/list #'(c ...)))]
    ;; Negation
    [(#%plain-app (~literal fake:not/c) c) (.not/c (go #'c))]
    [(#%plain-app (~literal fake:listof) c)
     (.μ/c 'X (.or/c .null/c (.cons/c (go #'c) (.x/c 'X))))]
    [(#%plain-app (~literal fake:list/c) c ...)
     (apply .list/c (go/list #'(c ...)))]
    [(begin (#%plain-app (~literal fake:dynamic-struct/c) tag:id c ...) _ ...)
     (.struct/c (.id (syntax-e #'tag) (cur-mod)) (go/list #'(c ...)))]
    [(#%plain-app (~literal fake:=/c) c) (.comp/c '= (go #'c))]
    [(#%plain-app (~literal fake:>/c) c) (.comp/c '> (go #'c))]
    [(#%plain-app (~literal fake:>=/c) c) (.comp/c '>= (go #'c))]
    [(#%plain-app (~literal fake:</c) c) (.comp/c '< (go #'c))]
    [(#%plain-app (~literal fake:<=/c) c) (.comp/c '<= (go #'c))]
    [(#%plain-app (~literal fake:cons/c) c d) (.cons/c (go #'c) (go #'d))]
    [(#%plain-app (~literal fake:one-of/c) c ...) (apply .one-of/c (go/list #'(c ...)))]
    ; recursive contract reference. FIXME: code duplicate
    [(let-values () (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...)
     (.x/c (syntax-e #'x))]
    [(begin (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...)
     (.x/c (syntax-e #'x))]
    [(#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...)
     (.x/c (syntax-e #'x))]

    ;; primitive contracts
    [(~literal fake:any/c) .any/c]
    
    ;; Literals
    [v:str (.b (syntax->datum #'v))]
    [v:number (.b (syntax->datum #'v))]
    [v:boolean (.b (syntax->datum #'v))]
    ;; Ignore sub-modules
    [(module _ ...) (todo 'submodule)]
    [(module* _ ...) (todo 'module*)]
    [(#%declare _) (todo '#%declare)]
    [_
     #:when (prefab-struct-key (syntax-e #'v))
     (todo 'struct)]
    [(#%plain-app f x ...)
     (.@ (go #'f) (go/list #'(x ...)) (cur-mod))]
    [((~literal with-continuation-mark) e₀ e₁ e₂)
     (.wcm (go #'e₀) (go #'e₁) (go #'e₂))]
    [(begin e ...) (-begin (go/list #'(e ...)))]
    [(begin0 e₀ e ...) (.begin0 (go #'e₀) (go/list #'(e ...)))]
    [(if i t e) (.if (go #'i) (go #'t) (go #'e))]
    [(let-values () b ...) (-begin (go/list #'(b ...)))]
    [(let-values (bindings ...) b ...)
     (define ctx′ ctx)
     (.let-values
      (for/list ([binding (in-list (syntax->list #'(bindings ...)))])
        (syntax-parse binding
          [((x ...) e)
           (begin0
               (cons (length (syntax->list #'(x ...))) (go #'e))
             (set! ctx′ (ext-env ctx′ (syntax->list #'(x ...)))))]))
      (-begin (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
                (parse-expr bᵢ ctx′)))
      (cur-mod))]
    [(#%plain-lambda fmls b ...+)
     (define-values (arity ctx′) (parse-formals ctx #'fmls))
     (.λ arity
         (-begin (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
                   (parse-expr bᵢ ctx′))))]
    
    [(case-lambda [fml bodies ...+] ...)
     (.case-lambda
      (for/list ([fmlᵢ (in-list (syntax->list #'(fml ...)))]
                 [bodiesᵢ (in-list (syntax->list #'((bodies ...) ...)))])
        ;; Compute case arity and extended context for RHS
        (define-values (arity ctx′) (parse-formals ctx fmlᵢ))
        (cons arity
              (-begin (for/list ([body (in-list (syntax->list bodiesᵢ))])
                        (parse-expr body ctx′))))))]
    [(letrec-values () b ...) (-begin (go/list #'(b ...)))]
    [(letrec-values (bindings ...) b ...)
     (define bnds (syntax->list #'(bindings ...)))
     (define-values (total-xs ctx′)
       (for/fold ([total-xs 0] [ctx′ ctx]) ([bnd (in-list bnds)])
         (syntax-parse bnd
           [((x ...) e)
            (define xs (syntax->list #'(x ...)))
            (values (+ total-xs (length xs)) (ext-env ctx′ xs))])))
     (.letrec-values
      (for/list ([bnd (in-list bnds)])
        (syntax-parse bnd
          [((x ...) eₓ) (cons (length (syntax->list #'(x ...))) (parse-expr #'eₓ ctx′))]))
      (-begin (for/list ([e (in-list (syntax->list #'(b ...)))])
                (parse-expr e ctx′)))
      (cur-mod))]
    [(quote e) (parse-quote #'e)]
    [(quote-syntax e) (todo 'quote-syntax)]
    [((~literal #%top) . id)
     (error "Unknown identifier ~a in module ~a" (syntax->datum #'id) (cur-mod))]
    [(#%variable-reference) (todo '#%variable-reference)]
    [(#%variable-reference id) (todo (format "#%variable-reference ~a" (syntax->datum #'id)))]
    
    ;; Hacks for now
    [(~literal null) .null]
    [(~literal null?) .null/c]
    [(~literal empty) .null]
    [(~literal empty?) .null/c]
    [(~literal positive?) (go #'(#%plain-lambda (x) (#%plain-app > x 0)))]
    [(~literal negative?) (go #'(#%plain-lambda (x) (#%plain-app > x 0)))]
    [(~literal zero?) (go #'(#%plain-lambda (x) (#%plain-app = x 0)))]
    
    [i:identifier
     (or
      (parse-primitive #'i)
      (match (identifier-binding #'i)
        ['lexical (.x (id->sd ctx #'i))]
        [#f (.x (id->sd ctx #'i))]
        [(list (app (λ (x)
                      (parameterize ([current-directory (directory-part (cur-mod))])
                        (mod-path->mod-name
                         (resolved-module-path-name (module-path-index-resolve x)))))
                    src)
               _ _ _ _ _ _)
         (.ref (.id (syntax-e #'i) src) (cur-mod))]))]))

(define/contract (parse-quote stx)
  (scv-syntax? . -> . .expr?)
  (syntax-parse stx
    [e:number (.b (syntax-e #'e))]
    [e:str (.b (syntax-e #'e))]
    [e:boolean (.b (syntax-e #'e))]
    [e:id (.b (syntax-e #'e))]
    [e:keyword (.b (syntax-e #'e))]
    [(l . r)
     (.@ .cons (list (parse-quote #'l) (parse-quote #'r)) (cur-mod))]
    [() .null]
    [e (error 'parse-quote "unsupported quoted form: ~a" (syntax-e #'e))]))

;; Parse given `formals` to extend environment
(define/contract (parse-formals ctx formals)
  (env? scv-syntax? . -> . (values .formals? env?))
  (syntax-parse formals
    [(x:id ...)
     (define xs (syntax->list #'(x ...)))
     (values (length xs) (ext-env ctx xs))]
    [rest:id
     (values (cons 0 'rest) (ext-env ctx (list #'rest)))]
    [(x:id ... . rest:id)
     (define xs (append (syntax->list #'(x ...)) (list #'rest)))
     (values (cons (- (length xs) 1) 'rest) (ext-env ctx xs))]))

(define/contract (parse-primitive id)
  (identifier?  . -> . (or/c #f .o?))
  (log-debug "parse-primitive: ~a~n~n" (syntax->datum id))
  (syntax-parse id
    [(~literal number?) 'number?]
    [(~literal real?) 'real?]
    [(~literal integer?) 'integer?]
    [(~literal false?) 'false?]
    [(~literal not) 'false?]
    [(~literal boolean?) 'boolean?]
    [(~literal string?) 'string?]
    [(~literal symbol?) 'symbol?]
    [(~literal procedure?) 'procedure?]
    [(~literal add1) 'add1]
    [(~literal sub1) 'sub1]
    [(~literal string-length) 'string-length]
    [(~literal sqrt) 'sqrt]
    [(~literal equal?) 'equal?]
    [(~literal =) '=]
    [(~literal >) '>]
    [(~literal <) '<]
    [(~literal >=) '>=]
    [(~literal <=) '<=]
    [(~literal +) '+]
    [(~literal -) '-]
    [(~literal *) '*]
    [(~literal /) '/]
    [(~literal expt) 'expt]
    [(~literal abs) 'abs]
    [(~literal min) 'min]
    [(~literal max) 'max]
    #;[(~literal set-box!) 'set-box!]
    [(~literal cons) .cons]
    [(~or (~literal car) (~literal unsafe-car)) .car]
    [(~or (~literal cdr) (~literal unsafe-cdr)) .cdr]
    [(~literal cons?) .cons?]
    [(~literal values) 'values]
    ;; Temporary ops
    [(~literal sqr) 'sqr]
    [_ #f]))

(define/contract (parse-provide-spec spec)
  (scv-syntax? . -> . .provide-spec?)
  (printf "Warning: shouldn't reach `parse-provide-spec` if using `fake-contract`~n")
  (syntax-parse spec
    [i:identifier #'i]
    [_ (error 'parse-provide-spec "unexpected: ~a" spec)]))

(define/contract (parse-require-spec spec)
  (scv-syntax? . -> . .require-spec?)
  (syntax-parse spec
    [i:identifier (syntax-e #'i)]
    [_ (log-debug "parse-require-spec: ignore ~a~n" (syntax->datum spec)) 'dummy-require]))

;; Extends environment
(define/contract (ext-env ctx xs)
  (env? (listof identifier?) . -> . env?)
  
  (for/fold ([ctx′ ctx]) ([x (in-list xs)])
    (cons x ctx′)))

;; Return static distance of given identifier in context
(define/contract (id->sd ctx id)
  (env? identifier? . -> . integer?)
  (or (for/first ([idᵢ (in-list ctx)] [i (in-naturals)]
                  #:when (free-identifier=? id idᵢ))
        i)
      (error 'id->sd "Unbound identifier ~a" (syntax->datum id))))

;; For debugging only. Return scv-relevant s-expressions
(define/contract (scv-relevant path)
  (path-string? . -> . any/c)
  (define stx (do-expand-file path))
  (for/list ([stxᵢ (in-list (syntax->list stx))]
             #:unless (scv-ignore? stxᵢ))
    (syntax->datum stxᵢ)))

;; Testing only
(define (test . files)
  (files->prog files))