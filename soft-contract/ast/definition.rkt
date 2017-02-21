#lang typed/racket/base

(provide (all-defined-out)
         (all-from-out "arity.rkt"))

(require racket/match
         racket/set
         racket/list
         racket/string
         racket/extflonum 
         racket/splicing
         "../utils/main.rkt"
         "arity.rkt"
         "srcloc.rkt")

(require/typed/provide racket/undefined
  [undefined Undefined])

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

;; Temporary definition of module path
(define-type -l (U Symbol String))
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
(-formals . ::= . (Listof Symbol)
                  (-varargs [init : (Listof Symbol)] [rest : Symbol]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Base . ::= . Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Char Null Void Arity EOF Undefined)

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

(-provide-spec . ::= . (-p/c-item [id : Symbol] [spec : -e] [loc : ℓ]))

(-require-spec . ::= . -l #|TODO|#)

(-e . ::= . -v
            (-x Symbol) ; lexical variables 
            -𝒾 ; module references
            (-@ -e (Listof -e) ℓ)
            (-if -e -e -e)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e])
            (-letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e])
            (-set! (U -𝒾 -x) -e)
            (-error String)
            
            ;; contract stuff
            (-μ/c Symbol -e)
            (--> [doms : (Listof -e)] [rng : -e] [loc : ℓ])
            (-->i [doms : (Listof -e)] [rng : -λ] [loc : ℓ])
            (-case-> [clauses : (Listof (Pairof (Listof -e) -e))] ℓ)
            (-x/c.tmp Symbol) ; hack
            (-x/c Symbol)
            (-struct/c [name : -𝒾] [fields : (Listof -e)] [loc : ℓ])

            ;; internal use only
            (-ar -e -e))

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
           (-st-mk -𝒾)
           ;; internal use only
           (-st/c-ac -𝒾 Index)
           (-->i-ac-dom Index)
           (-->i-ac-rng)
           (-->-ac-dom Index)
           (-->-ac-rng)
           (-ar-ctc)
           (-ar-fun))

(define -𝒾-values (-𝒾 'values 'Λ))
(define -𝒾-cons (-𝒾 'cons 'Λ))
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
    [(or (regexp? x) (pregexp? x) (bytes? x)) (format "~a" x)]
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
   [(-st-ac (== -𝒾-cons) 0) 'car]
   [(-st-ac (== -𝒾-cons) 1) 'cdr]
   [(-st-ac (== -𝒾-box) _) 'unbox]
   [(-st-ac 𝒾 i) (format-symbol "~a@~a" (-𝒾-name 𝒾) i)]
   [(-st-p 𝒾) (format-symbol "~a?" (-𝒾-name 𝒾))]
   [(-st-mut (== -𝒾-box) _) 'set-box!]
   [(-st-mut 𝒾 i) (format-symbol "set-~a-~a!" (-𝒾-name 𝒾) i)]
   ;; internals
   [(-st/c-ac 𝒾 i) (format-symbol "~a/c@~a" (-𝒾-name 𝒾) i)]
   [(-->i-ac-dom i) (format-symbol "->i~a" (n-sub i))]
   [(-->i-ac-rng) '->iᵣ]
   [(-->-ac-dom i) (format-symbol "->~a" (n-sub i))]
   [(-->-ac-rng) '->ᵣ]
   [(-ar-ctc) 'ar-ctc]
   [(-ar-fun) 'ar-fun]))

(define (show-e [e : -e]) : Sexp
  (match e
    ; syntactic sugar
    [(-λ (list x) (-@ 'not (list (-@ f (list (-x x)) _)) _)) `(not/c ,(show-e f))]
    [(-λ (list x) (-@ '= (list (-x x) e*) _)) `(=/c ,(show-e e*))]
    [(-λ (list x) (-@ (or 'equal? 'eq? 'eqv?) (list (-x x) e*) _)) `(≡/c ,(show-e e*))]
    [(-λ (list x) (-@ '> (list (-x x) e*) _)) `(>/c ,(show-e e*))]
    [(-λ (list x) (-@ '< (list (-x x) e*) _)) `(</c ,(show-e e*))]
    [(-λ (list x) (-@ '>= (list (-x x) e*) _)) `(≥/c ,(show-e e*))]
    [(-λ (list x) (-@ '<= (list (-x x) e*) _)) `(≤/c ,(show-e e*))]
       
    [(-if a b (-b #f))
     (match* ((show-e a) (show-e b))
       [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
       [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
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
    [(-x x) x]
    [(-𝒾 x p)
     (case p ;; hack
       [(Λ) (format-symbol "_~a" x)]
       [else x])]
    [(-let-values bnds body)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-letrec-values bnds body)
     `(letrec-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-set! x e) `(set! ,(show-e x) ,(show-e e))]
    [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
    [(-begin es) `(begin ,@(show-es es))]
    [(-begin0 e es) `(begin ,(show-e e) ,@(show-es es))]
    [(-error msg) `(error ,msg)]
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-μ/c x c) `(μ/c (,x) ,(show-e c))]
    [(--> cs d _)
     `(,@(map show-e cs) . -> . ,(show-e d))]
    [(-->i cs (and d (-λ xs _)) _)
     (match xs
       [(? list? xs)
        `(,@(map show-e cs) ↦ ,(show-e d))]
       [(-varargs xs₀ x)
        (define-values (cs₀ c) (split-at cs (length xs₀)))
        `(,@(map show-e cs₀) #:rest ,@(map show-e c) ↦ ,(show-e d))])]
    [(-case-> clauses _)
     (for/list : (Listof Sexp) ([clause clauses])
       (match-define (cons cs d) clause)
       `(,@(map show-e cs) . -> . ,(show-e d)))]
    [(-x/c.tmp x) x]
    [(-x/c x) x]
    [(-struct/c 𝒾 cs _)
     `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(show-es cs))]
    ;; internals
    [(-ar c e) `(ar ,(show-e c) ,(show-e e))]))

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
    [(-p/c-item x c _) `(,x ,(show-e c))]))

(define show-require-spec : (-require-spec → Sexp)
  values)

(define show-formals : (-formals → Sexp)
  (match-lambda
    [(-varargs xs rst) (cons xs rst)]
    [(? list? l) l]))
