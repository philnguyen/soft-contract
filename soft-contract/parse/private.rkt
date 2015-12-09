#lang racket
(require
 racket/unsafe/ops
 web-server/private/util
 "../utils/debug.rkt" "../utils/pretty.rkt" "../utils/set.rkt"
 "../primitives/declarations.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 ;; For extra constants
 racket/undefined racket/extflonum
 (only-in redex/reduction-semantics variable-not-in)
 syntax/parse syntax/modresolve
 "expand.rkt"
 (prefix-in fake: "../fake-contract.rkt")
 (for-syntax racket/base racket/match racket/list racket/set syntax/parse racket/contract
             "../primitives/declarations.rkt"))
(provide (all-defined-out))

(define/contract (files->modules paths)
  ((listof path-string?) . -> . (listof -module?))
  (for/list ([path (in-list paths)])
    (parse-top-level-form (do-expand-file path))))

(define/contract cur-mod (parameter/c string? #|TODO|#)
  (make-parameter "top-level"))

(define scv-syntax? (and/c syntax? (not/c scv-ignore?)))

;; Read our current limited notion of program
(define/contract (parse-prog mods top)
  ((listof scv-syntax?) scv-syntax? . -> . -prog?)
  (-prog (parse-mods mods) (parse-e top)))

(define/contract (parse-mods mods)
  ((listof scv-syntax?) . -> . (listof -module?))
  (todo 'parse-mods))

(define (mod-path->mod-name p)
  (match p ; hacks
    ['#%kernel 'Λ]
    ['#%unsafe 'unsafe]
    [(and (? symbol?) (app symbol->string "expanded module")) (cur-mod)]
    [_ (path->string (simplify-path p))]))

(define/contract (parse-top-level-form form)
  (scv-syntax? . -> . -top-level-form?)
  (log-debug "parse-top-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path (#%plain-module-begin forms ...))
     (define mod-name (mod-path->mod-name (syntax-source #'id)))
     (-module
      mod-name
      (parameterize ([cur-mod mod-name])
        (-plain-module-begin
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
     (-begin/simp (map parse-top-level-form (syntax->list #'(form ...))))]
    [((~literal #%expression) e) (parse-e #'e)]
    [_ (parse-general-top-level-form form)]))

(define/contract (parse-module-level-form form)
  (scv-syntax? . -> . (or/c #f -module-level-form?))
  (log-debug "parse-module-level-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare #%plain-lambda #%plain-app
                call-with-values)
    [(#%provide spec ...)
     (-provide (cur-mod) (map parse-provide-spec (syntax->list #'(spec ...))))]
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
     (-provide (cur-mod)
               (for/list ([x (in-list (syntax->datum #'(x ...)))]
                          [c (in-list (syntax->list #'(c ...)))])
                 (-p/c-item x (parse-e c))))]
    
    [_ (or (parse-general-top-level-form form)
           (parse-submodule-form form))]))

(define/contract (parse-submodule-form form)
  (scv-syntax? . -> . (or/c #f -submodule-form?))
  (log-debug "parse-submodule-form:~n~a~n~n" (pretty (syntax->datum form)))
  (syntax-parse form
    [((~literal module) id path ((~literal #%plain-module-begin) d ...))
     (-module
      (path->string (simplify-path (syntax-source #'id)))
      (-plain-module-begin (map parse-module-level-form (syntax->list #'(d ...)))))]
    [((~literal module*) _ ...) (todo 'module*)]
    [_ #f]))

(define/contract (parse-general-top-level-form form)
  (scv-syntax? . -> . (or/c #f -general-top-level-form?))
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
     (define si (-struct-info (-id ctor-name (cur-mod)) n ∅))
     (-define-values
      (cur-mod)
      (list* ctor-name (syntax-e #'pred) (map syntax-e accs))
      (-@ (-ref (-id 'values 'Λ) (cur-mod) (next-neg!))
          (list* (-st-mk si)
                 (-st-p si)
                 (for/list ([(accᵢ i) (in-indexed accs)])
                   (-st-ac si i)))
          -Λ))]
    [(define-values (x:identifier) e) ; FIXME: separate case hack to "close" recursive contract
     (define lhs (syntax-e #'x))
     (define rhs (parse-e #'e))
     (define frees (free-x/c rhs))
     (cond
       [(set-empty? frees)
        (-define-values (cur-mod) (list lhs) rhs)]
       [(set-empty? (set-remove frees lhs))
        (define pos (next-neg!))
        (-define-values (cur-mod) (list lhs)
           (-μ/c pos (e/ (-x/c.tmp lhs) (-x/c pos) rhs)))]
       [else
        (error 'TODO
               "In ~a's definition: arbitrary reference (recursive-contract ~a) not supported for now."
               lhs (set-first (set-remove frees lhs)))])]
    [(define-values (x:identifier ...) e)
     (-define-values (cur-mod) (syntax->datum #'(x ...)) (parse-e #'e))]
    [(#%require spec ...)
     (-require (map parse-require-spec (syntax->list #'(spec ...))))]
    [(define-syntaxes _ ...) #f] 
    [_ (parse-e form)]))

(define/contract (parse-e stx)
  (scv-syntax? . -> . -e?)
  (log-debug "parse-e: ~a~n~n" (pretty-format (syntax->datum stx)))

  (define/contract (parse-es es)
    ((and/c scv-syntax? (not/c identifier?)) . -> . (listof -e?))
    (map parse-e (syntax->list es)))

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
     (--> (parse-es #'(c ...)) (parse-e #'d) (next-neg!))]
    ;; Dependent contract
    [(~or (begin
            (#%plain-app
             (~literal fake:dynamic->i)
             (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
             (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
            _ ...)
          (let-values ()
            (#%plain-app
             (~literal fake:dynamic->i)
             (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
             (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...))
            _ ...)
          (#%plain-app
           (~literal fake:dynamic->i)
           (#%plain-app list [#%plain-app list (quote x:id) cₓ:expr] ...)
           (#%plain-lambda (z:id ...) d:expr #|FIXME temp hack|# _ ...)))
     (-->i (map cons (syntax->datum #'(z ...)) (parse-es #'(cₓ ...)))
           #f
           (parse-e #'d)
           (next-neg!))]
    [(#%plain-app (~literal fake:listof) c)
     (-listof (cur-mod) (parse-e #'c))]
    [(#%plain-app (~literal fake:list/c) c ...)
     (-list/c (parse-es #'(c ...)))]
    [(#%plain-app (~literal fake:box/c) c)
     (-box/c (parse-e #'c))]
    [(#%plain-app (~literal fake:vector/c) c ...)
     (-@ (-ref (-id 'vector/c 'Λ) (cur-mod) (next-neg!))
         (parse-es #'(c ...))
         (-src-loc (cur-mod) (next-neg!)))]
    [(#%plain-app (~literal fake:vectorof) c)
     (-@ (-ref (-id 'vectorof 'Λ) (cur-mod) (next-neg!))
         (parse-e #'c)
         (-src-loc (cur-mod) (next-neg!)))]
    [(begin (#%plain-app (~literal fake:dynamic-struct/c) tag:id c ...) _ ...)
     (define si (-struct-info (-id (syntax-e #'tag) (cur-mod))
                              (length (syntax->list #'(c ...)))
                              ∅))
     (-struct/c si (parse-es #'(c ...)) (next-neg!))]
    [(#%plain-app (~literal fake:=/c) c) (-comp/c '= (parse-e #'c))]
    [(#%plain-app (~literal fake:>/c) c) (-comp/c '> (parse-e #'c))]
    [(#%plain-app (~literal fake:>=/c) c) (-comp/c '>= (parse-e #'c))]
    [(#%plain-app (~literal fake:</c) c) (-comp/c '< (parse-e #'c))]
    [(#%plain-app (~literal fake:<=/c) c) (-comp/c '<= (parse-e #'c))]
    [(#%plain-app (~literal fake:cons/c) c d)
     (-cons/c (parse-e #'c) (parse-e #'d))]
    [(#%plain-app (~literal fake:one-of/c) c ...)
     (-one-of/c (cur-mod) (parse-es #'(c ...)))]
    [(~or (let-values ()
            (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...)
          (begin (#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...) _ ...))
     (-x/c.tmp (syntax-e #'x))]
    [(#%plain-app (~literal fake:dynamic-recursive-contract) x:id _ ...)
     (-x/c.tmp (syntax-e #'x))]

    ;; primitive contracts
    [(~literal fake:any/c) 'any/c]
    [(~literal fake:none/c) 'none/c]
    
    ;; Literals
    [v:str (-b (syntax->datum #'v))]
    [v:number (-b (syntax->datum #'v))]
    [v:boolean (-b (syntax->datum #'v))]
    ;; Ignore sub-modules
    [(module _ ...) (todo 'submodule)]
    [(module* _ ...) (todo 'module*)]
    [(#%declare _) (todo '#%declare)]
    [_
     #:when (prefab-struct-key (syntax-e #'v))
     (todo 'struct)]
    [(#%plain-app f x ...)
     (-@ (parse-e #'f)
         (parse-es #'(x ...))
         (-src-loc (cur-mod) (syntax-position stx)))]
    [((~literal with-continuation-mark) e₀ e₁ e₂)
     (-wcm (parse-e #'e₀) (parse-e #'e₁) (parse-e #'e₂))]
    [(begin e ...) (-begin/simp (parse-es #'(e ...)))]
    [(begin0 e₀ e ...) (-begin0 (parse-e #'e₀) (parse-es #'(e ...)))]
    [(if i t e) (-if (parse-e #'i) (parse-e #'t) (parse-e #'e))]
    [(let-values () b ...) (-begin/simp (parse-es #'(b ...)))]
    [(let-values (bindings ...) b ...)
     (-let-values
      (for/list ([binding (in-list (syntax->list #'(bindings ...)))])
        (syntax-parse binding
          [((x ...) e) (cons (syntax->datum #'(x ...)) (parse-e #'e))]))
      (-begin/simp (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
                     (parse-e bᵢ)))
      (cur-mod))]
    [(set! x e) (-set! (syntax-e #'x) (parse-e #'e))]
    [(#%plain-lambda fmls b ...+)
     (-λ (parse-formals #'fmls)
         (-begin/simp
          (for/list ([bᵢ (in-list (syntax->list #'(b ...)))])
            (parse-e bᵢ))))]
    
    [(case-lambda [fml bodies ...+] ...)
     (-case-λ
      (for/list ([fmlᵢ (in-list (syntax->list #'(fml ...)))]
                 [bodiesᵢ (in-list (syntax->list #'((bodies ...) ...)))])
        ;; Compute case arity and extended context for RHS
        (cons (parse-formals fmlᵢ)
              (-begin/simp (for/list ([body (in-list (syntax->list bodiesᵢ))])
                        (parse-e body))))))]
    [(letrec-values () b ...) (-begin/simp (parse-es #'(b ...)))]
    [(letrec-values (bindings ...) b ...)
     (define bnds (syntax->list #'(bindings ...)))
     (-letrec-values
      (for/list ([bnd (in-list bnds)])
        (syntax-parse bnd
          [((x ...) eₓ) (cons (syntax->datum #'(x ...)) (parse-e #'eₓ))]))
      (-begin/simp (for/list ([e (in-list (syntax->list #'(b ...)))])
                     (parse-e e)))
      (cur-mod))]
    [(quote e) (parse-quote #'e)]
    [(quote-syntax e) (todo 'quote-syntax)]
    [((~literal #%top) . id)
     (error "Unknown identifier ~a in module ~a" (syntax->datum #'id) (cur-mod))]
    [(#%variable-reference) (todo '#%variable-reference)]
    [(#%variable-reference id) (todo (format "#%variable-reference ~a" (syntax->datum #'id)))]
    
    ;; Hacks for now
    [(~literal null) -null]
    [(~literal empty) -null]
    [(~literal fake:not/c) (-ref (-id 'not/c 'Λ) (cur-mod) (next-neg!))]
    [(~literal fake:and/c) (-ref (-id 'and/c 'Λ) (cur-mod) (next-neg!))]
    [(~literal fake:or/c ) (-ref (-id 'or/c  'Λ) (cur-mod) (next-neg!))]
    
    [i:identifier
     (or
      (parse-primitive #'i)
      (match (identifier-binding #'i)
        ['lexical (-x (syntax-e #'i))]
        [#f (-x (syntax-e #'i))]
        [(list (app (λ (x)
                      (parameterize ([current-directory (directory-part (cur-mod))])
                        ;(printf "part: ~a~n" (directory-part (cur-mod)))
                        ;(printf "id: ~a~n" #'i)
                        (mod-path->mod-name
                         (resolved-module-path-name (module-path-index-resolve x)))))
                    src)
               _ _ _ _ _ _)
         (when (equal? 'not/c (syntax-e #'i))
           (error "done"))
         (-ref (-id (syntax-e #'i) src) (cur-mod) (next-neg!))]))]))

(define/contract (parse-quote stx)
  (scv-syntax? . -> . -e?)
  (syntax-parse stx
    [e:number (-b (syntax-e #'e))]
    [e:str (-b (syntax-e #'e))]
    [e:boolean (-b (syntax-e #'e))]
    [e:id (-b (syntax-e #'e))]
    [e:keyword (-b (syntax-e #'e))]
    [(l . r)
     (-@ -cons
         (list (parse-quote #'l) (parse-quote #'r))
         (-src-loc (cur-mod) (syntax-position stx)))]
    [() -null]
    [e (error 'parse-quote "unsupported quoted form: ~a" (syntax-e #'e))]))

;; Parse given `formals` to extend environment
(define/contract (parse-formals formals)
  (scv-syntax? . -> . -formals?)
  (syntax-parse formals
    [(x:id ...) (syntax->datum #'(x ...))]
    [rest:id (-varargs '() (syntax-e #'rest))]
    [(x:id ... . rest:id) (-varargs (syntax->datum #'(x ...)) (syntax-e #'rest))]))

(define/contract (parse-primitive id)
  (identifier?  . -> . (or/c #f -ref? -b?))
  (log-debug "parse-primitive: ~a~n~n" (syntax->datum id))

  

  (define-syntax (make-parse-clauses stx)

    (syntax-parse stx
      [(_ id:id)
       ;; The reason we generate (syntax-parse) cases instead of set lookup
       ;; is to ensure that the source refers to the right reference

       (define/contract cache (hash/c symbol? any/c) (make-hash))

       (define/contract (make-clause dec)
         (any/c . -> . (listof syntax?))

         (define (make-ref s)
           (symbol? . -> . syntax?)
           #`(-ref (-id '#,s 'Λ) (cur-mod) (next-neg!)))
         
         (match dec
           [`(#:pred ,s ,_ ...)
            (list #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [`(#:alias ,s ,t)
            (list #`[(~literal #,s)
                     #,(hash-ref! cache t (λ () (error 'make-ref "~a aliases undeclared ~a" s t)))])]
           [`(#:batch (,ss ...) ,(? arr?) ,_ ...)
            (for/list ([s ss])
              #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [`(,(? symbol? s) ,(? base? c))
            (list #`[(~literal #,s) #,(hash-ref! cache s #`(-b #,s))])]
           [(or `(,(? symbol? s) ,_ ...)
                `(#:struct-cons ,s ,_)
                `(#:struct-pred ,s ,_)
                `(#:struct-acc  ,s ,_ ,_)
                `(#:struct-mut  ,s ,_ ,_))
            (list #`[(~literal #,s) #,(hash-ref! cache s (make-ref s))])]
           [r
            (log-warning "unhandled in `make-parse-clauses` ~a~n" r)
            '()]))
       (define ans 
         #`(syntax-parse id
             #,@(append-map make-clause prims)
             [_ #f]))
       
       ;(printf "parse-primitive:~n~a~n" (syntax->datum ans))
       
       ans]))

  ;; Read off from primitive table
  (make-parse-clauses id))

(define/contract (parse-provide-spec spec)
  (scv-syntax? . -> . -provide-spec?)
  (printf "Warning: shouldn't reach `parse-provide-spec` if using `fake-contract`~n")
  (syntax-parse spec
    [i:identifier #'i]
    [_ (error 'parse-provide-spec "unexpected: ~a" spec)]))

(define/contract (parse-require-spec spec)
  (scv-syntax? . -> . -require-spec?)
  (syntax-parse spec
    [i:identifier (syntax-e #'i)]
    [_ (log-debug "parse-require-spec: ignore ~a~n" (syntax->datum spec)) 'dummy-require]))

;; Full primitive module generated from primtive table
(define/contract init-prim (listof -module-level-form?)
  (let ()
    
    (define/contract cache
      (hash/c symbol? -e?)
      (make-hasheq))

    (define/contract (simple-parse s)
      (any/c . -> . -e?)
      (match s
        [`(-> ,doms ... ,rng)
         (--> (map simple-parse doms)
              (simple-parse rng)
              (next-neg!))]
        [`(->* (,doms ...) #:rest ,rst ,rng)
         (log-warning "Skipping ->* for now~n")
         'any/c]
        [`(and/c ,cs ...) (-and/c 'Λ (map simple-parse cs))]
        [`(or/c  ,cs ...) (-or/c  'Λ (map simple-parse cs))]
        [`(one-of/c ,cs ...) (-one-of/c 'Λ (map simple-parse cs))]
        [`(list/c ,cs ...) (-list/c (map simple-parse cs))]
        [`(cons/c ,c ,d) (-cons/c (simple-parse c) (simple-parse d))]
        [`(not/c ,c) (-not/c 'Λ (simple-parse c))]
        [`(listof ,c) (-listof (simple-parse c) (next-neg!))]
        [`(values ,ctcs ...)
         (-@ 'values (map simple-parse ctcs) (-src-loc 'Λ (next-neg!)))]
        [(? symbol? s) (-ref (-id s 'Λ) 'Λ (next-neg!))]
        [`(quote ,s) (-b s)]
        [(or (? number? x) (? boolean? x)) (-b x)]))

    (define/contract (mk-struct-info x)
      (any/c . -> . -struct-info?)
      (match-define `(,t ,mut?s ...) x)
      (-struct-info (-id t 'Λ) (length mut?s) (for/set ([(mut? i) (in-indexed mut?s)] #:when mut?) i)))

    (define/contract (make-defs dec)
      (any/c . -> . (listof -define-values?))
      (match dec
        
        [(or `(#:pred ,s ,_ ...)
             `(,(? symbol? s) ,(or (? arr?) (? arr*?)) ,_ ...))
         (list (-define-values 'Λ (list s) s))]
        [`(#:alias ,_ ,_) '()] ; taken care of
        [`(#:batch (,ss ...) ,_ ...)
         (for/list ([s ss])
           (-define-values 'Λ (list s) s))]
        [`(#:struct-cons ,s ,si)
         (list (-define-values 'Λ (list s) (-st-mk (mk-struct-info si))))]
        [`(#:struct-pred ,s ,si)
         (list (-define-values 'Λ (list s) (-st-p (mk-struct-info si))))]
        [`(#:struct-acc ,s ,si ,i)
         (list (-define-values 'Λ (list s) (-st-ac (mk-struct-info si) i)))]
        [`(#:struct-mut ,s ,si ,i)
         (list (-define-values 'Λ (list s) (-st-mut (mk-struct-info si) i)))]
        [r
         (log-warning "unhandled in `make-defs`: ~a~n" r)
         '()]))

    (define/contract (make-decs dec)
      (any/c . -> . (listof -p/c-item?))
      (match dec
        [`(#:pred ,s ,doms? ...)
         (define ctc
           (match doms?
             ['()
              ;; optimize `(any/c . -> . boolean?)` to `any/c`
              (hash-ref! cache s 'any/c)]
             [(list (list dom ...))
              ; optimize `boolean?` to `any/c`
              (hash-ref! cache s (--> (map simple-parse dom) 'any/c (next-neg!)))]))
         (list (-p/c-item s ctc))]
        [`(#:alias ,_ ,_) '()] ; taken care of
        [`(#:batch (,ss ...) ,sig ,_ ...)
         (define ctc (simple-parse sig))
         (for/list ([s ss])
           (-p/c-item s (hash-ref! cache s ctc)))]
        [`(,(? symbol? s) ,sig ,_ ...)
         (define ctc (hash-ref! cache s (simple-parse sig)))
         (list (-p/c-item s ctc))]
        [`(#:struct-cons ,s (,_ ,mut?s ...))
         (define ctc (hash-ref! cache s
                                (-->i (for/list ([i (length mut?s)])
                                        (cons (string->symbol (format "k•~a" (n-sub i)))
                                              'any/c))
                                      #f
                                      'any/c
                                      (next-neg!))))
         (list (-p/c-item s ctc))]
        [`(#:struct-pred ,s (,_ ,mut? ...))
         (define ctc (hash-ref! cache s (-->i (list (cons 'p• 'any/c)) #f 'any/c (next-neg!))))
         (list (-p/c-item s ctc))]
        [`(#:struct-acc ,s ,si ,_)
         (define ctc (hash-ref! cache s (-->i (list (cons 'a• (-st-p (mk-struct-info si))))
                                              #f
                                              'any/c
                                              (next-neg!))))
         (list (-p/c-item s ctc))]
        [`(#:struct-mut ,s ,si ,_)
         (define ctc (hash-ref! cache s (-->i (list (cons 'm•₁ (-st-p (mk-struct-info si)))
                                                    (cons 'm•₂ 'any/c))
                                              #f
                                              'any/c
                                              (next-neg!))))
         (list (-p/c-item s ctc))]
        [r
         (log-warning "unhandled in `make-decs` ~a~n" r)
         '()]))
    
    ;; HACK: leave provide last because `𝑰` is hacky for now
    `(,@(append-map make-defs prims)
      ,(-provide 'Λ (append-map make-decs prims)))))

;; For debugging only. Return scv-relevant s-expressions
(define/contract (scv-relevant path)
  (path-string? . -> . any/c)
  (define stx (do-expand-file path))
  (for/list ([stxᵢ (in-list (syntax->list stx))]
             #:unless (scv-ignore? stxᵢ))
    (syntax->datum stxᵢ)))

;; Testing only
(define (test . files)
  (files->modules files))
