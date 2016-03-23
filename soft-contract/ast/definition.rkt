#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set racket/list racket/function racket/extflonum 
 "../utils/main.rkt")

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

;; Temporary definition of module path
(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(struct Mon-Info ([pos : Mon-Party] [neg : Mon-Party] [src : Mon-Party]) #:transparent)

;; Swap positive and negative blame parties
(define swap-parties : (Mon-Info → Mon-Info)
  (match-lambda [(Mon-Info l+ l- lo) (Mon-Info l- l+ lo)]))

;; Source location
(define +ℓ! (make-neg-src))
(define next-subscript! (make-nat-src))
(define-type -ℓ Integer)

;; Symbol names are used for source code. Integers are used for generated.
;; Keep this eq?-able
(Var-Name . ::= . Symbol Integer)
(define +x! (make-nat-src))

;; Identifier as a name and its source
(struct -𝒾 ([name : Symbol] [ctx : Adhoc-Module-Path]) #:transparent)

;; Struct meta data
(struct -struct-info ([id : -𝒾] [arity : Natural] [mutables : (℘ Natural)]) #:transparent)

;; Formal parameters
(-formals . ::= . (Listof Var-Name)
                  (-varargs [init : (Listof Var-Name)] [rest : Var-Name]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Arity . ::= . Natural arity-at-least (Listof (U Natural arity-at-least)))
(Base . ::= . Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Char Null Void Arity)

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

(-submodule-form . ::= . (-module [path : Adhoc-Module-Path] [body : (Listof -module-level-form)]))

(-provide-spec . ::= . (-p/c-item [id : Symbol] [spec : -e] [loc : -ℓ]))

(-require-spec . ::= . Adhoc-Module-Path #|TODO|#)

(-e . ::= . -v
            (-x Var-Name) ; lexical variables 
            (-ref [id : -𝒾] [ℓ : -ℓ]) ; module references
            (-@ -e (Listof -e) -ℓ)
            (-if -e -e -e)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof (Pairof (Listof Var-Name) -e))] [body : -e])
            (-letrec-values [bnds : (Listof (Pairof (Listof Var-Name) -e))] [body : -e])
            (-set! Var-Name -e)

            (-error String)

            (-@-havoc -x) ; hack for havoc to detect argument's arity at runtime
            (-amb (℘ -e))
            
            ;; contract stuff
            (-μ/c -ℓ -e)
            (-->i [doms : (Listof -e)] [rng : -λ] [pos : -ℓ])
            (-x/c.tmp Symbol) ; hack
            (-x/c -ℓ)
            (-struct/c [info : -struct-info] [fields : (Listof -e)] [pos : -ℓ]))

(-v . ::= . -prim
            (-λ -formals -e)
            (-case-λ (Listof (Pairof -formals -e)))
            (-• Natural))

(-prim . ::= . ;; Represent *unsafe* operations without contract checks. 
               ;; User code shouldn't have direct access to these.
               ;; Generated `prim` module exports these operations wrapped in contract. -o (-b Base)
               -o
               ;; primitive values that can appear in syntax
               (-b [unboxed : Base]))

(-o . ::= . Symbol
           (-st-p -struct-info)
           (-st-ac -struct-info Natural)
           (-st-mut -struct-info Natural)
           (-st-mk -struct-info))

(define-type -es (℘ -e))

;; Current restricted representation of program
(struct -prog ([modules : (Listof -module)] [main : -e]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))
(define -void (-b (void)))

(define -𝒾-values (-𝒾 'values 'Λ))
(define -𝒾-cons (-𝒾 'cons 'Λ))
(define -s-cons (-struct-info -𝒾-cons 2 ∅))
(define -cons (-st-mk -s-cons))
(define -car (-st-ac -s-cons 0))
(define -cdr (-st-ac -s-cons 1))
(define -cons? (-st-p -s-cons))

(define -zero (-b 0))
(define -one (-b 1))

(define -𝒾-box (-𝒾 'box 'Λ))
(define -s-box  (-struct-info -𝒾-box 1 {set 0}))
(define -box? (-st-p -s-box))
(define -unbox (-st-ac -s-box 0))
(define -box (-st-mk -s-box))
(define -set-box! (-st-mut -s-box 0))

(: -cond : (Listof (Pairof -e -e)) -e → -e)
;; Make `cond` at object language level, expanding to `if`
(define (-cond cases default)
  (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
           (match-define (cons cnd thn) alt)
           (-if cnd thn els))
         default
         cases))

(: --> : (Listof -e) -e → -e)
;; Make a non-dependent contract as a special case of dependent contract
;; TODO: *special* construct for non-dependent contract with eagerly evaluated range
(define (--> cs d)
  (define xs (map (λ (_) (+x!)) cs))
  (-->i cs (-λ xs d) (+ℓ!)))

(: -->* : (Listof -e) -e -e → -e)
;; Make a non-dependent vararg contract
(define (-->* cs rst d)
  (define xs (-varargs (map (λ (_) (+x!)) cs) (+x!)))
  (-->i (append cs (list rst)) (-λ xs d) (+ℓ!)))

;; Make conjunctive and disjunctive contracts
(define-values (-and/c -or/c)
  (let () 
    (: -app/c : Symbol (Listof -e) → -e)
    (define (-app/c o es) : -e
      (match es
        ['() 'any/c]
        [(list e) e]
        [(cons e es*)
         (-@ (-ref (-𝒾 o 'Λ) (+ℓ!)) (list e (-app/c o es*)) (+ℓ!))]))
    (values (curry -app/c 'and/c) (curry -app/c 'or/c))))

(: -not/c : -e → -e)
(define (-not/c e)
  (-@ (-ref (-𝒾 'not/c 'Λ) (+ℓ!)) (list e) (+ℓ!)))

(: -one-of/c : (Listof -e) → -e)
(define (-one-of/c es)
  (match es
    [(list) 'none/c]
    [(list e)
     (define x (+x!))
     (-λ (list x) (-@ 'equal? (list (-x x) e) (+ℓ!)))]
    [(cons e es*)
     (define x (+x!))
     (-or/c (list (-λ (list x) (-@ 'equal? (list (-x x) e) (+ℓ!)))
                  (-one-of/c es*)))]))

(: -cons/c : -e -e → -e)
(define (-cons/c c d)
  (-struct/c -s-cons (list c d) (+ℓ!)))

(: -listof : -e → -e)
(define (-listof c)
  (define ℓ (+ℓ!))
  (-μ/c ℓ (-or/c (list 'null? (-cons/c c (-x/c ℓ))))))

(: -box/c : -e → -e)
(define (-box/c c)
  (-struct/c -s-box (list c) (+ℓ!)))

(: -list/c : (Listof -e) → -e)
(define (-list/c cs)
  (foldr -cons/c 'null? cs))

(: -list : (Listof -e) → -e)
(define (-list es)
  (match es
    ['() -null]
    [(cons e es*)
     (-@ -cons (list e (-list es*)) (+ℓ!))]))

(:* -and : -e * → -e)
;; Return ast representing conjuction of 2 expressions
(define -and
  (match-lambda*
    [(list) -tt]
    [(list e) e]
    [(cons e es) (-if e (apply -and es) -ff)]))

(: -comp/c : Symbol -e → -e)
;; Return ast representing `(op _ e)`
(define (-comp/c op e)
  (define x (+x!))
  (define 𝐱 (-x x))
  (-λ (list x)
      (-and (-@ 'real? (list 𝐱) (+ℓ!)) (-@ op (list 𝐱 e) (+ℓ!)))))

(: -amb/simp : (Listof -e) → -e)
;; Smart constructor for `amb` with simplification for 1-expression case
(define -amb/simp
  (match-lambda
    [(list e) e]
    [es (-amb (list->set es))]))

(: -amb/remember : (Listof -e) → -e)
;; Return ast representing "remembered" non-determinism
(define/match (-amb/remember es)
  [((list)) (-b 'end-of-amb)]
  [((list e)) e]
  [((cons e es)) (-if (•!) e (-amb/remember es))])

(: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
;; Smart constructor for begin, simplifying single-expression case
(define/match (-begin/simp xs)
  [((list e)) e]
  [(es) (-begin es)])

(: •! : → -•)
;; Generate new labeled hole
(define •!
  (let ([n : Natural 0])
    (λ () (begin0 (-• n) (set! n (+ 1 n))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty Printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-values (show-x/c show-x/c⁻¹ count-x/c) ((inst unique-sym -ℓ) 'x))

(define (show-ℓ [ℓ : -ℓ]) : Symbol
  (string->symbol (format "ℓ~a" (n-sub ℓ))))

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
    [else x]))

;; Return operator's simple show-o for pretty-printing
(define show-o : (-o → Symbol)
  (match-lambda
   [(? symbol? s) s]
   [(-st-mk s) (show-struct-info s)]
   [(-st-ac (== -s-cons) 0) 'car]
   [(-st-ac (== -s-cons) 1) 'cdr]
   [(-st-ac (== -s-box) 0) 'unbox]
   [(-st-ac s i) (string->symbol (format "~a@~a" (show-struct-info s) i))]
   [(-st-p s) (string->symbol (format "~a?" (show-struct-info s)))]
   [(-st-mut (== -s-box) 0) 'set-box!]
   [(-st-mut s i) (string->symbol (format "set-~a-~a!" (show-struct-info s) i))]))

(define (show-e [e : -e]) : Sexp
  (match e
    ; syntactic sugar
    [(-λ (list x) (-@ '= (list (-x x) e*) _)) `(=/c ,(show-e e*))]
    [(-λ (list x) (-@ 'equal? (list (-x x) e*) _)) `(≡/c ,(show-e e*))]
    [(-λ (list x) (-@ '> (list (-x x) e*) _)) `(>/c ,(show-e e*))]
    [(-λ (list x) (-@ '< (list (-x x) e*) _)) `(</c ,(show-e e*))]
    [(-λ (list x) (-@ '>= (list (-x x) e*) _)) `(≥/c ,(show-e e*))]
    [(-λ (list x) (-@ '<= (list (-x x) e*) _)) `(≤/c ,(show-e e*))]
    [(-@ (-λ (list x) (-x x)) (list e) _) (show-e e)]
    [(-@ (-λ (list x) (-if (-x x) (-x x) b)) (list a) _)
     (match* ((show-e a) (show-e b))
       [(`(or ,l ...) `(or ,r ...)) `(or ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(or ,l ...) r) `(or ,@(cast l Sexps) ,r)]
       [(l `(or ,r ...)) `(or ,l ,@(cast r Sexps))]
       [(l r) `(or ,l ,r)])]
    [(-@ (-st-mk (-struct-info (and n (or 'and/c 'or/c 'not/c)) _ _)) c* _)
     `(,n ,@(show-es c*))]
    [(-if a b (-b #f))
     (match* ((show-e a) (show-e b))
       [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
       [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
       [(l r) `(and ,l ,r)])]
    [(-if a b (-b #t)) `(implies ,(show-e a) ,(show-e b))]

    [(-λ xs e) `(λ ,(show-formals xs) ,(show-e e))]
    [(-• i) (string->symbol (format "•~a" (n-sub i)))]
    [(-b b) (show-b b)]
    [(? -o? o) (show-o o)]
    [(-x x)
     (cond [(symbol? x) (format-symbol "ₓ~a" x)]
           [else (format-symbol "𝐱~a" (n-sub x))])]
    [(-ref (-𝒾 x p) _)
     (case p ;; hack
       [(Λ) (string->symbol (format "_~a" x))]
       [else x])]
    [(-let-values bnds body)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-letrec-values bnds body)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-set! x e) `(set! ,x ,(show-e e))]
    [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
    [(-@-havoc x) `(havoc ,(show-e x))]
    [(-begin es) `(begin ,@(show-es es))]
    [(-begin0 e es) `(begin ,(show-e e) ,@(show-es es))]
    [(-error msg) `(error ,msg)]
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (show-e e)))]
    [(-μ/c x c) `(μ/c (,(show-x/c x)) ,(show-e c))]
    [(-->i cs (-λ xs d) _)
     (match xs
       [(? list? xs)
        `(,@(for/list : (Listof Sexp) ([c cs] [x xs])
              `(,x : ,(show-e c)))
          ↦ ,(show-e d))]
       [(-varargs xs₀ x)
        (define-values (cs₀ c) (split-at cs (length xs₀)))
        `(,@(for/list : (Listof Sexp) ([c cs₀] [x xs₀])
              `(,x : ,(show-e c)))
          #:rest `(,x : ,(show-e c))
          ↦ ,(show-e d))])]
    [(-x/c.tmp x) x]
    [(-x/c x) (show-x/c x)]
    [(-struct/c info cs _)
     `(,(string->symbol (format "~a/c" (show-struct-info info))) ,@(show-es cs))]))

(define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
  (for/list ([e es]) (show-e e)))

(define (show-module [m : -module]) : Sexp
  (match-define (-module path forms) m)
  `(module ,path
    ,@(map show-module-level-form forms)))

(define (show/c [s : Symbol]) : Symbol
  (string->symbol (format "~a/c" s)))

(define (show-struct-info [info : -struct-info]) : Symbol
  (-𝒾-name (-struct-info-id info)))

(define show-module-level-form : (-module-level-form → Sexp)
  (match-lambda
    [(-provide specs) `(provide ,@(map show-provide-spec specs))]
    [(? -general-top-level-form? m) (show-general-top-level-form m)]))

(define show-general-top-level-form : (-general-top-level-form → Sexp)
  (match-lambda
    [(? -e? e) (show-e e)]
    [(-define-values xs e) `(define-values ,xs ,(show-e e))]
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
