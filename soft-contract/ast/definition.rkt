#lang typed/racket/base

(provide (all-defined-out)
         (all-from-out "arity.rkt" "srcloc.rkt"))

(require racket/match
         racket/set
         racket/list
         racket/string
         racket/extflonum 
         racket/splicing
         bnf
         "../utils/pretty.rkt"
         "arity.rkt"
         "srcloc.rkt")

(require/typed/provide racket/undefined
  [undefined Undefined])

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

(struct (X) -var ([init : (Listof X)] [rest : X]) #:transparent)
(define-type (-maybe-var X) (U (Listof X) (-var X)))

(: -var-map (∀ (X Y)
               (case->
                [(X → Y) (Listof X) → (Listof Y)]
                [(X → Y) (-var X) → (-var Y)]
                [(X → Y) (-maybe-var X) → (-maybe-var Y)])))
(define (-var-map f xs)
  (match xs
    [(? list? xs) (map f xs)]
    [(-var xs x) (-var (map f xs) (f x))]))

(: shape (∀ (X) (-maybe-var X) → (U Index arity-at-least)))
(define shape
  (match-lambda [(? list? l) (length l)]
                [(-var xs _) (arity-at-least (length xs))]))

(struct -l³ ([pos : -l] [neg : -l] [src : -l]) #:transparent)

(: +x! : (U Symbol Integer) * → Symbol)
(define (+x! . prefixes)
  (define (stuff->string x) (format "~a" x))
  (define prefix (string-join (map stuff->string prefixes) "_" #:after-last "_"))
  (gensym prefix))

(: +x!/memo : (U Symbol Integer) * → Symbol)
(define +x!/memo
  (let ([m : (HashTable (Listof (U Symbol Integer)) Symbol) (make-hash)])
    (λ [xs : (U Symbol Integer) *]
      (hash-ref! m xs (λ () (apply +x! xs))))))

;; Identifier as a name and its source
(struct -𝒾 ([name : Symbol] [ctx : -l]) #:transparent)

;; Formal parameters
(define-type -formals (-maybe-var Symbol))
(define-predicate -formals? -formals)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Base . ::= . Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Byte-Regexp Byte-PRegexp Char Null Void Arity EOF Undefined)

(-top-level-form . ::= . -general-top-level-form
                         -e
                         -module
                         -begin/top)

(-module-level-form . ::= . -general-top-level-form
                            (-provide [specs : (Listof -provide-spec)])
                            -submodule-form)

(-general-top-level-form . ::= . -e
                                 (-define-values [ids : (Listof Symbol)] [e : -e])
                                 (-require (Listof -require-spec)))

(-submodule-form . ::= . (-module [path : -l] [body : (Listof -module-level-form)]))

(-provide-spec . ::= . (-p/c-item [id : Symbol] [spec : -e] [loc : ℓ])
                       Symbol)

(-require-spec . ::= . -l #|TODO|#)

(-e . ::= . -v
            (-x Symbol ℓ) ; lexical variables 
            (-ref -𝒾 ℓ) ; module references
            (-@ -e (Listof -e) ℓ)
            (-if -e -e -e)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof (Pairof (Listof Symbol) -e))]
                         [body : -e]
                         [loc : ℓ])
            (-letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))]
                            [body : -e]
                            [loc : ℓ])
            (-set! (U Symbol -𝒾) -e)
            (-error String ℓ)
            
            ;; contract stuff
            (-μ/c Symbol -e)
            (--> [doms : (-maybe-var -e)] [rng : -e] [loc : ℓ])
            (-->i [doms : (Listof -e)] [rng : -λ] [loc : ℓ])
            (-case-> [clauses : (Listof (Pairof (Listof -e) -e))] ℓ)
            (-x/c.tmp Symbol) ; hack
            (-x/c Symbol)
            (-struct/c [name : -𝒾] [fields : (Listof -e)] [loc : ℓ])

            )

(-v . ::= . -prim
            (-λ -formals -e)
            (-case-λ (Listof (Pairof (Listof Symbol) -e)))
            (-•))

(-prim . ::= . -o
               ;; primitive values that can appear in syntax
               (-b [unboxed : Base]))

;; Primitive operations
(-o . ::= . Symbol
           (-st-p -𝒾)
           (-st-ac -𝒾 Index)
           (-st-mut -𝒾 Index)
           (-st-mk -𝒾))

(define -𝒾-values (-𝒾 'values 'Λ))
(define -𝒾-cons (-𝒾 'cons 'Λ))
(define -𝒾-mcons (-𝒾 'mcons 'Λ))
(define -𝒾-box (-𝒾 'box 'Λ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty Printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-b [x : Base]) : Sexp
  (cond
    [(string? x) (format "\"~a\"" x)]
    [(or (symbol? x) (keyword? x)) `(quote ,x)]
    [(and (real? x) (inexact? x))
     (define s (number->string x))
     (substring s 0 (min (string-length s) 5))]
    [(or (regexp? x) (pregexp? x) (byte-regexp? x) (byte-pregexp? x) (bytes? x)) (format "~a" x)]
    [(extflonum? x) (extfl->inexact x)]
    [(void? x) 'void]
    [(arity-at-least? x) `(arity-at-least ,(arity-at-least-value x))]
    [(list? x) `(list ,@(map show-b x))]
    [(eof-object? x) '⟪eof⟫]
    [(defined? x) x]
    [else 'undefined]))

;; Return operator's simple show-o for pretty-printing
(define show-o : (-o → Symbol)
  (match-lambda
    [(? symbol? s) s]
    [(-st-mk 𝒾) (-𝒾-name 𝒾)]
    [(-st-ac 𝒾 i) (show-ac 𝒾 i)]
    [(-st-p 𝒾) (format-symbol "~a?" (-𝒾-name 𝒾))]
    [(-st-mut (== -𝒾-mcons) 0) 'set-mcar!]
    [(-st-mut (== -𝒾-mcons) 1) 'set-mcdr!]
    [(-st-mut (== -𝒾-box) _) 'set-box!]
    [(-st-mut 𝒾 i) (format-symbol "set-~a._~a!" (-𝒾-name 𝒾) i)]))

(define (show-ac [𝒾 : (U -𝒾 Symbol)] [i : Index]) : Symbol
  (match* (𝒾 i)
    [((== -𝒾-cons) 0) 'car]
    [((== -𝒾-cons) 1) 'cdr]
    [((== -𝒾-mcons) 0) 'mcar]
    [((== -𝒾-mcons) 1) 'mcdr]
    [((== -𝒾-box) _) 'unbox]
    [(𝒾 i) (format-symbol "~a._~a" (if (symbol? 𝒾) 𝒾 (-𝒾-name 𝒾)) i)]))

(define (show-e [e : -e]) : Sexp
  (match e
    ; syntactic sugar
    [(-λ (list x) (-@ 'not (list (-@ f (list (-x x _)) _)) _)) `(not/c ,(show-e f))]
    [(-λ (list x) (-@ '= (list (-x x _) e*) _)) `(=/c ,(show-e e*))]
    [(-λ (list x) (-@ (or 'equal? 'eq? 'eqv?) (list (-x x _) e*) _)) `(≡/c ,(show-e e*))]
    [(-λ (list x) (-@ '> (list (-x x _) e*) _)) `(>/c ,(show-e e*))]
    [(-λ (list x) (-@ '< (list (-x x _) e*) _)) `(</c ,(show-e e*))]
    [(-λ (list x) (-@ '>= (list (-x x _) e*) _)) `(≥/c ,(show-e e*))]
    [(-λ (list x) (-@ '<= (list (-x x _) e*) _)) `(≤/c ,(show-e e*))]
       
    [(-if a b (-b #f))
     (match* ((show-e a) (show-e b))
       [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l (Listof Sexp)) ,@(cast r (Listof Sexp)))]
       [(`(and ,l ...) r) `(and ,@(cast l (Listof Sexp)) ,r)]
       [(l `(and ,r ...)) `(and ,l ,@(cast r (Listof Sexp)))]
       [(l r) `(and ,l ,r)])]
    [(-if a b (-b #t)) `(implies ,(show-e a) ,(show-e b))]

    [(-λ xs e) `(λ ,(show-formals xs) ,(show-e e))]
    [(-case-λ clauses)
     `(case-lambda
        ,@(for/list : (Listof Sexp) ([clause clauses])
            (match-define (cons xs e) clause)
            `(,(show-formals xs) ,(show-e e))))]
    [(-•) '•]
    [(-b b) (show-b b)]
    [(? -o? o) (show-o o)]
    [(-x x _) x]
    [(-ref (-𝒾 x p) _)
     (case p ;; hack
       [(Λ) (format-symbol "_~a" x)]
       [else x])]
    [(-let-values bnds body _)
     (match bnds
       [(list (cons (list lhs) rhs) ...)
        `(let ,(for/list : (Listof Sexp) ([x (in-list lhs)]
                                          [e (in-list rhs)])
                 `(,(assert x symbol?) ,(show-e (assert e -e?))))
           ,(show-e body))]
       [_
        `(let-values
             ,(for/list : (Listof Sexp) ([bnd bnds])
                (match-define (cons xs ex) bnd)
                `(,xs ,(show-e ex)))
           ,(show-e body))])]
    [(-letrec-values bnds body _)
     (match bnds
       [(list (cons (list lhs) rhs) ...)
        `(letrec ,(for/list : (Listof Sexp) ([x (in-list lhs)]
                                             [e (in-list rhs)])
                    `(,(assert x symbol?) ,(show-e (assert e -e?))))
           ,(show-e body))]
       [_
        `(letrec-values
             ,(for/list : (Listof Sexp) ([bnd bnds])
                (match-define (cons xs ex) bnd)
                `(,xs ,(show-e ex)))
           ,(show-e body))])]
    [(-set! x e) `(set! ,(if (symbol? x) x (-𝒾-name x)) ,(show-e e))]
    [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
    [(-begin es) `(begin ,@(show-es es))]
    [(-begin0 e es) `(begin0 ,(show-e e) ,@(show-es es))]
    [(-error msg _) `(error ,msg)]
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-μ/c x c) `(μ/c (,x) ,(show-e c))]
    [(--> dom rng _)
     (match dom
       [(-var es e)
        `(,(map show-e es) #:rest ,(show-e e) . ->* . ,(show-e rng))]
       [(? list? es)
        `(,@(map show-e es) . -> . ,(show-e rng))])]
    [(-->i cs (and d (-λ xs _)) _)
     (match xs
       [(? list? xs)
        `(,@(map show-e cs) ↦ ,(show-e d))]
       [(-var xs₀ x)
        (define-values (cs₀ c) (split-at cs (length xs₀)))
        `(,@(map show-e cs₀) #:rest ,@(map show-e c) ↦ ,(show-e d))])]
    [(-case-> clauses _)
     (for/list : (Listof Sexp) ([clause clauses])
       (match-define (cons cs d) clause)
       `(,@(map show-e cs) . -> . ,(show-e d)))]
    [(-x/c.tmp x) x]
    [(-x/c x) x]
    [(-struct/c 𝒾 cs _)
     `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(show-es cs))]))

(define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
  (for/list ([e es]) (show-e e)))

(define (show-module [m : -module]) : (Listof Sexp)
  (match-define (-module path forms) m)
  `(module ,path
    ,@(map show-module-level-form forms)))

(define show-module-level-form : (-module-level-form → Sexp)
  (match-lambda
    [(-provide specs) `(provide ,@(map show-provide-spec specs))]
    [(? -general-top-level-form? m) (show-general-top-level-form m)]))

(define show-general-top-level-form : (-general-top-level-form → Sexp)
  (match-lambda
    [(? -e? e) (show-e e)]
    [(-define-values xs e)
     (match* (xs e)
       [((list f) (-λ xs e*)) `(define (,f ,@(show-formals xs)) ,(show-e e*))]
       [((list x) _) `(define ,x ,(show-e e))]
       [(_ _) `(define-values ,xs ,(show-e e))])]
    [(-require specs) `(require ,@(map show-require-spec specs))]))

(define show-provide-spec : (-provide-spec → Sexp)
  (match-lambda
    [(-p/c-item x c _) `(,x ,(show-e c))]
    [(? symbol? x) x]))

(define show-require-spec : (-require-spec → Sexp)
  values)

(define show-formals : (-formals → Sexp)
  (match-lambda
    [(-var xs rst) (cons xs rst)]
    [(? list? l) l]))

(define show-𝒾 : (-𝒾 → Symbol)
  (match-lambda
    [(-𝒾 name from) (format-symbol "~a@~a" name from)]))

(: show-values-lift (∀ (X) (X → Sexp) → (Listof X) → Sexp))
(define (show-values-lift show-elem)
  (match-lambda
    [(list x) (show-elem x)]
    [xs `(values ,@(map show-elem xs))]))

(define show-values (show-values-lift show-e))
