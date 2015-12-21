#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set racket/function racket/extflonum 
 "../utils/untyped-macros.rkt" "../utils/sexp-stx.rkt" "../utils/def.rkt" "../utils/pretty.rkt" "../utils/set.rkt")

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

;; Temporary definition of module path
(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(define-type Mon-Info (List Mon-Party Mon-Party Mon-Party))

;; Swap positive and negative blame parties
(define (swap-parties [info : Mon-Info]) : Mon-Info
  (match-define (list + - o) info)
  (list - + o))

;; Source location
(struct -src-loc ([party : Mon-Party] [pos : Integer]) #:transparent)
(define -Λ (-src-loc 'Λ (next-neg!)))

;; Identifier as a name and where it's from
(struct -id ([name : Symbol] [ctx : Adhoc-Module-Path]) #:transparent)

;; Struct meta data
(struct -struct-info ([id : -id] [arity : Natural] [mutables : (Setof Integer)]) #:transparent)

;; Formal parameters
(define-data -formals
  (Listof Symbol)
  (struct -varargs [init : (Listof Symbol)] [rest : Symbol]))

;; Return all variable names in function's parameter list
(define (-formal-names [xs : -formals]) : (Setof Symbol)
  (match xs
    [(? list?) (list->set xs)]
    [(-varargs xs* x) (set-add (list->set xs*) x)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type/pred Base
  (U Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Char Null Void
     arity-at-least))

(define-data -top-level-form
  -general-top-level-form
  -e
  -module
  -begin/top)

(define-data -module-level-form
  -general-top-level-form
  (struct -provide [from : Adhoc-Module-Path] [specs : (Listof -provide-spec)])
  -submodule-form)

(define-data -general-top-level-form
  -e
  (struct -define-values [from : Adhoc-Module-Path] [ids : (Listof Symbol)] [e : -e])
  (struct -require [specs : (Listof -require-spec)]))

(define-data -submodule-form
  (struct -module [path : Adhoc-Module-Path] [body : -plain-module-begin]))

(define-data -provide-spec
  (struct -p/c-item [id : Symbol] [spec : -e]))

(define-data -require-spec
  Adhoc-Module-Path #|TODO|#)

(struct -plain-module-begin ([body : (Listof -module-level-form)]) #:transparent)

(define-data -e
  (subset: -v
    (struct -λ [formals : -formals] [body : -e])
    (struct -case-λ [body : (Listof (Pairof -formals -e))])
    (struct -• [l : (U Natural Symbol)])
    (subset: -prim
      ;; primitive values that can appear in syntax
      (struct -b [unboxed : Base])
      ;; Represent *unsafe* operations without contract checks. 
      ;; User code shouldn't have direct access to these.
      ;; Generated `prim` module exports these operations wrapped in contract.
      (subset: -o
        ; fixed
        Symbol
        ; user extensible
        (struct -st-p [info : -struct-info])
        (struct -st-ac [info : -struct-info] [index : Integer])
        (struct -st-mut [info : -struct-info] [index : Integer])
        (struct -st-mk [info : -struct-info]))))
  ;; lexical variables
  (struct -x [name : Symbol])
  ;; module references
  (struct -ref [id : -id] [ctx : Mon-Party] [pos : Integer])
  (struct -@ [f : -e] [xs : (Listof -e)] [loc : -src-loc])
  (struct -if [i : -e] [t : -e] [e : -e])
  (struct -wcm [key : -e] [val : -e] [body : -e])
  -begin/e
  (struct -begin0 [e0 : -e] [es : (Listof -e)])
  (struct -quote [v : Any])
  (struct -let-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -set! [x : Symbol] [e : -e])

  (struct -@-havoc [x : -x]) ; hack for havoc to detect argument's arity at runtime
  (struct -amb [es : -es])
  
  ;; contract stuff
  (struct -μ/c [pos : Integer] [c : -e])
  (struct -->i
    [dom : (Listof (Pairof Symbol -e))]
    [rest-dom : (Option (Pairof Symbol -e))]
    [rng : -e]
    [pos : Integer])
  (struct -x/c.tmp [x : Symbol]) ; hack
  (struct -x/c [pos : Integer])
  (struct -struct/c [info : -struct-info] [fields : (Listof -e)] [pos : Integer]))

(define-type -es (Setof -e))

;; Current restricted representation of program
(struct -prog ([modules : (Listof -module)] [main : -e]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))

(define -id-values (-id 'values 'Λ))
(define -id-cons (-id 'cons 'Λ))
(define -s-cons (-struct-info -id-cons 2 ∅))
(define -cons (-st-mk -s-cons))
(define -car (-st-ac -s-cons 0))
(define -cdr (-st-ac -s-cons 1))
(define -cons? (-st-p -s-cons))

(define -zero (-b 0))
(define -one (-b 1))

(define -id-box (-id 'box 'Λ))
(define -s-box  (-struct-info -id-box 1 {set 0}))
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

(: --> : Symbol (Listof -e) -e → -e)
;; Make a non-dependent contract as a special case of dependent contract
(define (--> prefix cs d)
  (define doms
    (for/list : (Listof (Pairof Symbol -e)) ([(c i) (in-indexed cs)])
      (define x (string->symbol (format "~a•~a" prefix (n-sub i)))) ; hack
      (cons x c)))
  (-->i doms #f d (next-neg!)))

(: -->* : (Listof -e) -e -e → -e)
;; Make a non-dependnet vararg contract
(define (-->* cs rst d)
  (define doms
    (for/list : (Listof (Pairof Symbol -e)) ([(c i) (in-indexed cs)])
      (define x (string->symbol (format "v•~a" (n-sub i))))
      (cons x c)))
  (define x-rst (string->symbol (format "rst•~a" (n-sub (length cs)))))
  (-->i doms (cons x-rst rst) d (next-neg!)))

;; Make conjunctive and disjunctive contracts
(define-values (-and/c -or/c)
  (let () 
    (define (-app/c [o : Symbol] [l : Mon-Party] [es : (Listof -e)]) : -e
      (match es
        ['() 'any/c]
        [(list e) e]
        [(cons e es*)
         (-@ (-ref (-id o 'Λ) l (next-neg!))
             (list e (-app/c o l es*))
             (-src-loc l (next-neg!)))]))
    (values (curry -app/c 'and/c)
            (curry -app/c 'or/c))))

(: -not/c : Mon-Party -e → -e)
(define (-not/c l e)
  (-@ (-ref (-id 'not/c 'Λ) l (next-neg!)) (list e) (-src-loc l (next-neg!))))

(: -one-of/c : Mon-Party (Listof -e) → -e)
(define (-one-of/c l es)
  (match es
    [(list) 'none/c]
    [(list e) (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ))]
    [(cons e es*)
     (-or/c l (list (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ))
                    (-one-of/c l es*)))]))

(: -cons/c : -e -e → -e)
(define (-cons/c c d)
  (-struct/c -s-cons (list c d) (next-neg!)))

(: -listof : Mon-Party -e → -e)
(define (-listof l c)
  (define pos (next-neg!))
  (-μ/c pos (-or/c l (list 'null? (-cons/c c (-x/c pos))))))

(: -box/c : -e → -e)
(define (-box/c c)
  (-struct/c -s-box (list c) (next-neg!)))

(: -list/c : (Listof -e) → -e)
(define (-list/c cs)
  (foldr -cons/c 'null? cs))

(: -list : Mon-Party (Listof -e) → -e)
(define (-list l es)
  (match es
    ['() -null]
    [(cons e es*)
     (-@ -cons (list e (-list l es*)) (-src-loc l (next-neg!)))]))

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
  (define x (string->symbol (format "~a•~a" op (n-sub (next-nat!)))))
  (-λ (list x) (-and (-@ 'real? (list (-x x)) -Λ) (-@ op (list (-x x) e) -Λ))))

(: -amb/simp : (Listof -e) → -e)
;; Smart constructor for `amb` with simplification for 1-expression case
(define -amb/simp
  (match-lambda
    [(list e) e]
    [es (-amb (list->set es))]))

(: -amb/remember : (Listof -e) → -e)
;; Return ast representing "remembered" non-determinism
(define/match (-amb/remember es)
  [((list)) -ff]
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

(define show-x/c : (Integer → Symbol) (unique-name 'x))

(define (show-src-loc [loc : -src-loc]) : Symbol
  (match-define (-src-loc lab pos) loc)
  (string->symbol (format "~a~a" lab (if pos (n-sub pos) ""))))

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
    [else x]))

;; Return operator's simple show-o for pretty-printing
(define show-o : (-o → Symbol)
  (match-lambda
   [(? symbol? s) s]
   [(-st-mk s) (show-struct-info s)]
   [(-st-ac (≡ -s-cons) 0) 'car]
   [(-st-ac (≡ -s-cons) 1) 'cdr]
   [(-st-ac (≡ -s-box) 0) 'unbox]
   [(-st-ac s i) (string->symbol (format "~a@~a" (show-struct-info s) i))]
   [(-st-p s) (string->symbol (format "~a?" (show-struct-info s)))]
   [(-st-mut (≡ -s-box) 0) 'set-box!]
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
    [(-λ (list x) (-@ 'arity-includes? (list (-x x) (-b 0)) _)) `(arity-includes/c ,x)]
    [(-λ (list x) (-@ 'arity=? (list (-x x) (-b 0)) _)) `(arity=/c ,x)]
    [(-λ (list x) (-@ 'arity>=? (list (-x x) (-b 0)) _)) `(arity≥/c ,x)]
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

    [(-λ (list xs ...) e) `(λ ,xs ,(show-e e))]
    [(-λ (-varargs xs rest) e) `(λ ,(cons xs rest) ,(show-e e))]
    [(-• ℓ)
     (cond
       [(integer? ℓ) (string->symbol (format "•~a" (n-sub ℓ)))]
       [else (string->symbol (format "•_~a" ℓ))])]
    [(-b b) (show-b b)]
    [(? -o? o) (show-o o)]
    [(-x x) (string->symbol (format "ₓ~a" x))]
    [(-ref (-id x p) _ _)
     (case p ;; hack
       [(Λ) (string->symbol (format "「~a」" x))]
       [else x])]
    [(-let-values bnds body _)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-letrec-values bnds body _)
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
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (show-e e)))]
    [(-μ/c x c) `(μ/c (,(show-x/c x)) ,(show-e c))]
    [(-->i doms _ rng _) `(,@(for/list : (Listof Sexp) ([dom doms])
                               (match-define (cons x c) dom)
                               `(,x : ,(show-e c)))
                           ↦ ,(show-e rng))]
    [(-x/c.tmp x) x]
    [(-x/c x) (show-x/c x)]
    [(-struct/c info cs _)
     `(,(string->symbol (format "~a/c" (show-struct-info info))) ,@(show-es cs))]))

(define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
  (for/list ([e es]) (show-e e)))

(define (show/c [s : Symbol]) : Symbol
  (string->symbol (format "~a/c" s)))

(define (show-struct-info [info : -struct-info]) : Symbol
  (-id-name (-struct-info-id info)))

(define show-module-level-form : (-module-level-form → Sexp)
  (match-lambda
    [(-provide _ specs) `(provide ,@(map show-provide-spec specs))]
    [(? -general-top-level-form? m) (show-general-top-level-form m)]))

(define show-general-top-level-form : (-general-top-level-form → Sexp)
  (match-lambda
    [(? -e? e) (show-e e)]
    [(-define-values _ xs e) `(define-values ,xs ,(show-e e))]
    [(-require specs) `(require ,@(map show-require-spec specs))]))

(define show-provide-spec : (-provide-spec → Sexp)
  (match-lambda
    [(-p/c-item x c) `(,x ,(show-e c))]))

(define show-require-spec : (-require-spec → Sexp)
  values)

