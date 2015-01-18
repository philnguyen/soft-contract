#lang racket/base
(require racket/match racket/list racket/set racket/bool
         "utils.rkt" "lang.rkt" (only-in redex/reduction-semantics variable-not-in)
         syntax/parse racket/pretty racket/contract
         "expand.rkt"
         (prefix-in fake: "fake-contract.rkt"))
(provide (all-defined-out) #;read-p #;on-•!)

#;(define (printf . _) (void))

;; TODO For testing only

#;(define on-•! (make-parameter (λ () '•)))

(define cur-mod (make-parameter #f))

(define (index->path i)
  (define-values (v _) (module-path-index-split i))
  (list (resolved-module-path-name (module-path-index-resolve i)) #f))

(define (todo x)
  (error 'TODO "~a" x))

(define scv-syntax? (and/c syntax? (not/c scv-ignore?)))

;; Read our current limited notion of program
(define/contract (read-prog mods top)
  ((listof scv-syntax?) scv-syntax? . -> . .prog?)
  (.prog (read-mods mods) (read-expr top)))

(define/contract (read-mods mods)
  ((listof scv-syntax?) . -> . (listof .module?))
  (todo 'read-mods))

(define/contract (read-top-level-form form)
  (scv-syntax? . -> . .top-level-form?)
  #;(printf "read-top-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path (#%plain-module-begin forms ...))
     (.module
      (module-path #'id)
      (.#%plain-module-begin
       (filter
        values
        (for/list ([formᵢ (in-list (syntax->list #'(forms ...)))]
                   #:when
                   (syntax-parse formᵢ
                     [((~literal module) (~literal configure-runtime) _ ...) #f]
                     [_ #t])
                   #:when
                   (scv-syntax? formᵢ))
          (read-module-level-form formᵢ)))
       #;(map read-module-level-form (syntax->list #'(forms ...)))))]
    [((~literal begin) form ...)
     (-begin (map read-top-level-form (syntax->list #'(form ...))))]
    [((~literal #%expression) e) (read-expr #'e)]
    [_ (read-general-top-level-form form)]))

(define/contract (read-module-level-form form)
  (scv-syntax? . -> . (or/c #f .module-level-form?))
  #;(printf "read-module-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                call-with-values)
    [(#%provide spec ...)
     (.#%provide (map read-provide-spec (syntax->list #'(spec ...))))]
    [(#%declare _ ...) (todo '#%declare)]
    [(begin-for-syntax _ ...) #|ignore|# #f]
    
    ;; Hack for reading our fake-contracts:
    [(#%plain-app
      call-with-values
      (#%plain-lambda
       ()
       (#%plain-app
        _
        (#%plain-app (~literal list) x:id c) ...))
      _)
     #;(printf "x: ~a~nc: ~a~n"
             (identifier? (car (syntax->list #'(x ...))))
             (identifier? (car (syntax->list #'(c ...)))))
     (.#%provide (for/list ([x (in-list (syntax->list #'(x ...)))]
                            [c (in-list (syntax->list #'(c ...)))])
                   (.p/c-item x (read-expr c))))]
    
    [_ (or (read-general-top-level-form form)
           (read-submodule-form form))]))

(define/contract (read-submodule-form form)
  (scv-syntax? . -> . (or/c #f .submodule-form?))
  #;(printf "read-submodule-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path ((~literal #%plain-module-begin) d ...))
     (.module
      (module-path #'id)
      (.#%plain-module-begin (map read-module-level-form (syntax->list #'(d ...)))))]
    [((~literal module*) _ ...) (todo 'module*)]
    [_ #f]))

(define/contract (read-general-top-level-form form)
  (scv-syntax? . -> . (or/c #f .general-top-level-form?))
  #;(printf "read-general-top-level-form:~n~a~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (define-syntaxes define-values #%require let-values #%plain-app values
                 call-with-values)
    [(define-values (_ ctor pred acc ...)
       (let-values ([(_ ...)
                     (let-values ()
                       (let-values ()
                         (#%plain-app _ ctor-name _ ...)))])
         (#%plain-app values _ _ _ (#%plain-app _ _ _ _) ...)))
     (define/contract ctor-name symbol? (syntax->datum #'ctor-name))
     (define/contract ctor identifier? (datum->syntax #'ctor ctor-name))
     (define/contract accs (listof identifier?) (syntax->list #'(acc ...)))
     (define n (length accs))
     (.define-values
      (list* ctor #'pred accs)
      (.@ (datum->syntax ctor 'values)
              (list* (.st-mk ctor n)
                     (.st-p ctor n)
                     (for/list ([accᵢ (in-list accs)] [i (in-naturals)])
                       (.st-ac ctor n i)))
              'Λ))]
    [(define-values (x:identifier ...) e)
     (.define-values (syntax->list #'(x ...)) (read-expr #'e))]
    [(#%require spec ...)
     (.#%require (map read-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes _ ...) #f] 
    [_ (read-expr form)]))

(define/contract (module-path stx)
  (identifier? . -> . module-path?)
  
  (syntax-parse stx
    [i:identifier
     (match (identifier-binding #'i)
       [(and X (list (app index->path (list src self?)) _ _ _ _ _ _))
        #;(error 'debug "binding: ~a~n" (first X))
        (.ref #'i (path->string (simplify-path src)) (cur-mod))]
       [#f #|FIXME|# (syntax->datum stx)])]))

(define/contract (read-expr stx [ctx '()])
  (scv-syntax? . -> . .expr?)
  #;(printf "read-expr: ~a~n~n" (pretty (syntax->datum stx)))
  ;;(: go : Syntax → .e)
  (define (go e) (read-expr e ctx))
  ;;(: go/list : Syntax → (Listof .e))
  (define (go/list es) (map go (syntax->list es)))
  (syntax-parse stx
    #:literals
    (let-values letrec-values begin0 if #%plain-lambda #%top
                module* module #%plain-app quote #%require quote-syntax
                with-continuation-mark #%declare #%provide case-lambda
                #%variable-reference set! list)
    ;;; Contracts
    ;; Non-dependent function contract
    [(let-values ([(_) #|TODO|# _]
                  [(_) (#%plain-app list c ...)]
                  [(_) (#%plain-app list d)])
       _ ...)
     (.-> (map read-expr (syntax->list #'(c ...)))
          (read-expr #'d))]
    ;; Conjunction
    [(#%plain-app (~literal fake:and/c) c ...)
     (match (map read-expr (syntax->list #'(c ...)))
       ['() .any/c]
       [(list c) c]
       [(list c₁ ... cₖ) (foldr .and/c cₖ c₁)])]
    ;; Disjunction
    [(#%plain-app (~literal fake:or/c) c ...)
     (match (map read-expr (syntax->list #'(c ...)))
       ['() .none/c]
       [(list c) c]
       [(list c₁ ... cₖ) (foldr .or/c cₖ c₁)])]
    
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
    [(#%plain-app f x ...) (.@ (go #'f) (go/list #'(x ...)) ctx)]
    [((~literal with-continuation-mark) e₀ e₁ e₂)
     (.wcm (go #'e₀) (go #'e₁) (go #'e₂))]
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
                (read-expr bᵢ ctx′))))]
    [(#%plain-lambda (fmls ...) b ...)
     (define xs (syntax->list #'(fmls ...)))
     (define ctx′ (ext-env ctx xs))
     (.λ
      (length xs)
      (-begin (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
                (read-expr bᵢ ctx′))))]
    [(case-lambda _ ...) (todo 'case-lambda)]
    [(letrec-values _ ...) (todo 'letrec-values)]
    [(quote e:number) (.b (syntax->datum #'e))]
    [(quote e:str) (.b (syntax->datum #'e))]
    [(quote e:boolean) (.b (syntax->datum #'e))]
    [(quote e:id) (.b (syntax->datum #'e))]
    [(quote e) #|FIXME|# (printf "Misread ~a as ~a:~n" (syntax->datum #'e) #f) (.b #f #|FIXME|#)]
    [(quote-syntax e) (todo 'quote-syntax)]
    [((~literal #%top) . id)
     (error "Unknown identifier ~a in module ~a" (syntax->datum #'id) (cur-mod))]
    [(#%variable-reference) (todo '#%variable-reference)]
    [(#%variable-reference id) (todo 'id)]
    [(~literal null) #|hack|# .null]
    [i:identifier
     (or
      (read-primitive #'i)
      (match (identifier-binding #'i)
        ['lexical (.x (id->sd ctx #'i))]
        [#f (.x (id->sd ctx #'i))]
        [(and X (list (app index->path (list src self?)) _ _ _ _ _ _))
         (printf "Identifier: ~a~nName: ~a~nPath: ~a~n~n"
                 #'i
                 (syntax->datum #'i)
                 (if (path? src)
                     (path->string (simplify-path src #f))
                     src))
         (define idsym (id->sym #'i))
         (define modsym (symbol->string (syntax-e stx)))
         (define path
           (cond [(path? src) (path->string (simplify-path src #f))]
                 [(eq? src '#%kernel) '#%kernel #|hack|#]
                 [src (symbol->string src)]
                 [else 'null]))
         (.ref #'i path (cur-mod))]))]))

(define/contract (read-primitive id)
  (identifier?  . -> . (or/c #f .o?))
  #;(printf "read-primitive: ~a~n~n" (syntax->datum id))
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
    [(~literal cons) (.st-mk #'cons 2)]
    [(~literal car) (.st-ac #'cons 2 0)]
    [(~literal cdr) (.st-ac #'cons 2 1)]
    [(~literal cons?) (.st-p #'cons 2)]
    [(~literal values) 'values]
    [_ #f]))

(define/contract (read-provide-spec spec)
  (scv-syntax? . -> . .raw-provide-spec?)
  (syntax-parse spec
    [i:identifier #'i]
    [_ (error 'read-provide-spec "unexpected: ~a" spec)]))

(define/contract (read-require-spec spec)
  (scv-syntax? . -> . .raw-require-spec?)
  (syntax-parse spec
    [i:identifier spec]
    [_ (printf "read-require-spec: ignore ~a~n" (syntax->datum spec) #f)]))

;; Extends environment
(define/contract (ext-env ctx xs)
  ((listof identifier?) (listof identifier?) . -> . (listof identifier?))
  
  (for/fold ([ctx′ ctx]) ([x (in-list xs)])
    (cons x ctx′)))

;; Return static distance of given identifier in context
(define/contract (id->sd ctx id)
  ((listof identifier?) identifier? . -> . integer?)
  ;(printf "id->sd: looking for ~a in context ~a~n" (syntax->datum id) (map syntax->datum ctx))
  (or (for/first ([idᵢ (in-list ctx)] [i (in-naturals)]
                  #:when (free-identifier=? id idᵢ))
        i)
      (error 'id->sd "Unbound identifier ~a" (syntax->datum id))))

(define stx (box #f))

;; Testing only
(module+ test
  (define (test file)
    (read-top-level-form (do-expand-file file)))

  (set-box! stx (test "test/test-parser/tests/provide-contract.rkt"))) 
