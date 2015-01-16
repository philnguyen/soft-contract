#lang racket/base
(require racket/match racket/list racket/set racket/bool
         "utils.rkt" "lang.rkt" (only-in redex/reduction-semantics variable-not-in)
         syntax/parse racket/pretty racket/contract
         "expand.rkt")
(provide (all-defined-out) #;read-p #;on-•!)

;; TODO For testing only

#;(define on-•! (make-parameter (λ () '•)))

(define cur-mod (make-parameter #f))

(define (index->path i)
  (define-values (v _) (module-path-index-split i))
  (list (resolved-module-path-name (module-path-index-resolve i)) #f))

(define (todo x)
  (error 'TODO "~a" x))

#;(define (ignore x)
  (printf "Ignore ~a~n" x)
  #f)

;;(: read-top-level-form : Syntax → .top-level-form)
(define/contract (read-top-level-form form)
  (syntax? . -> . .top-level-form?)
  (printf "read-top-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path (#%plain-module-begin forms ...))
     (.module
      #'id (lang-path #'path)
      (.#%plain-module-begin
       (filter-not false? (for/list ([formᵢ (in-list (syntax->list #'(forms ...)))]
                  #:when
                  (syntax-parse formᵢ
                    [((~literal module) (~literal configure-runtime) _ ...) #f]
                    [_ #t]))
         (read-module-level-form formᵢ)))
       #;(map read-module-level-form (syntax->list #'(forms ...)))))]
    [((~literal begin) form ...)
     (-begin (map read-top-level-form (syntax->list #'(form ...))))]
    [((~literal #%expression) e) (read-expr #'e)]
    [_ (read-general-top-level-form form)]))

;;(: read-module-level-form : Syntax → (Option .module-level-form))
(define/contract (read-module-level-form form)
  (syntax? . -> . (or/c #f .module-level-form?))
  (printf "read-module-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal #%provide) spec ...)
     (.#%provide (map read-provide-spec (syntax->list #'(spec ...))))]
    [((~literal #%declare) _ ...) (todo '#%declare)]
    [((~literal begin-for-syntax) _ ...) #|ignore|# #f]
    [_ (or (read-general-top-level-form form)
           (read-submodule-form form))]))

;;(: read-submodule-form : Syntax → (Option .submodule-form))
(define/contract (read-submodule-form form)
  (syntax? . -> . (or/c #f .submodule-form?))
  (printf "read-submodule-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path ((~literal #%plain-module-begin) d ...))
     (.module
      #'id (lang-path #'path)
      (.#%plain-module-begin (map read-module-level-form (syntax->list #'(d ...)))))]
    [((~literal module*) _ ...) (todo 'module*)]
    [_ #f]))

;;(: read-general-top-level-form : Syntax → (Option .general-top-level-form))
(define/contract (read-general-top-level-form form)
  (syntax? . -> . (or/c #f .general-top-level-form?))
  (printf "read-general-top-level-form:~n~a~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (define-syntaxes define-values #%require let-values #%plain-app values)
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
      (.#%app (datum->syntax ctor 'values)
              (list* (.st-mk ctor n)
                     (.st-p ctor n)
                     (for/list ([accᵢ (in-list accs)] [i (in-naturals)])
                       (.st-ac ctor n i)))
              'Λ))]
    [(define-values (x:identifier ...) e)
     (printf "Case 2~n")
     (.define-values (syntax->list #'(x ...)) (read-expr #'e))]
    [(#%require spec ...)
     (.#%require (map read-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes _ ...) #f]
    [_ (read-expr form)]))

(define/contract (lang-path stx)
  (identifier? . -> . module-path?)
  
  (syntax-parse stx
    [i:identifier
     (match (identifier-binding #'i)
       [(and X (list (app index->path (list src self?)) _ _ _ _ _ _))
        (.ref #'i (path->string (simplify-path src)) (cur-mod))]
       [#f #|FIXME|# (syntax->datum stx)])]))

;;(: read-expr ([Syntax] [(Listof Identifier)] . ->* . (Option .e)))
(define/contract (read-expr stx [ctx '()])
  (syntax? . -> . .expr?)
  (printf "read-expr:~n~a~n~n" (pretty (syntax->datum stx)))
  ;;(: go : Syntax → .e)
  (define (go e) (read-expr e ctx))
  ;;(: go/list : Syntax → (Listof .e))
  (define (go/list es) (map go (syntax->list es)))
  (syntax-parse stx
    #:literals
    (let-values letrec-values begin0 if #%plain-lambda #%top
                module* module #%plain-app quote #%require quote-syntax
                with-continuation-mark #%declare #%provide case-lambda
                #%variable-reference set!)
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
    [(#%plain-app f x ...) (.#%app (go #'f) (go/list #'(x ...)) ctx)]
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
             (set! ctx′ (bind ctx′ (syntax->list #'(x ...)))))]))
      (-begin (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
                (read-expr bᵢ ctx′))))]
    [(#%plain-lambda (fmls ...) b ...)
     (define xs (syntax->list #'(fmls ...)))
     (define ctx′ (bind ctx xs))
     (.#%plain-lambda
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
    [i:identifier
     (match (identifier-binding #'i)
       ['lexical (.x (id->sd ctx #'i))]
       [#f (.x (id->sd ctx #'i))]
       [(and X (list (app index->path (list src self?)) _ _ _ _ _ _))
        
        (define idsym (id->sym #'i))
        (define modsym (symbol->string (syntax-e stx)))
        (define path
          (cond [(path? src) (path->string (simplify-path src #f))]
                [(eq? src '#%kernel) '#%kernel #|hack|#]
                [src (symbol->string src)]
                [else 'null]))
        (.ref #'i path (cur-mod))])]))

(define/contract (read-provide-spec spec)
  (syntax? . -> . .raw-provide-spec?)
  (syntax-parse spec
    [i:identifier spec]
    [_ (printf "read-provide-spec: ignore ~a~n" (syntax->datum spec)) #f]))

(define/contract (read-require-spec spec)
  (syntax? . -> . .raw-require-spec?)
  (syntax-parse spec
    [i:identifier spec]
    [_ (printf "read-require-spec: ignore ~a~n" (syntax->datum spec) #f)]))

;;(: bind : (Listof Identifier) (Listof Identifier) → (Listof Identifier))
;; Extends environment
(define/contract (bind ctx xs)
  ((listof identifier?) (listof identifier?) . -> . (listof identifier?))
  
  (for/fold ([ctx′ ctx]) ([x (in-list xs)])
    (cons x ctx′)))

;;(: id->sd : (Listof Identifier) Identifier → Natural)
;; Return static distance of given identifier in context
(define/contract (id->sd ctx id)
  ((listof identifier?) identifier? . -> . integer?)
  ;(printf "id->sd: looking for ~a in context ~a~n" (syntax->datum id) (map syntax->datum ctx))
  (or (for/first ([idᵢ (in-list ctx)] [i (in-naturals)]
                  #:when (free-identifier=? id idᵢ))
        i)
      (error 'id->sd "Unbound identifier ~a" (syntax->datum id))))

(define (test file)
  (read-top-level-form (do-expand-file file)))
