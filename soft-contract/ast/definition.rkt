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
         "arity.rkt")

(require/typed/provide racket/undefined
  [undefined Undefined])

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

;; Temporary definition of module path
(define-type -l (U Symbol String))
(struct -l³ ([pos : -l] [neg : -l] [src : -l]) #:transparent)

;; Swap positive and negative blame parties
(define swap-parties : (-l³ → -l³)
  (match-lambda [(-l³ l+ l- lo) (-l³ l- l+ lo)]))

(define-new-subtype -ℓ (+ℓ Natural))

(splicing-local
    ((define n : Natural 1)
     (define m : (HashTable (Listof Any) -ℓ) (make-hash))
     ;; Just for debugging
     (define m⁻¹ : (HashTable -ℓ (Listof Any)) (make-hasheq)))

  (: +ℓ! : → -ℓ)
  (define (+ℓ!)
    (begin0 (+ℓ n)
      (set! n (+ 1 n))))

  ;; Hack to remember fixed location for havoc
  (: +ℓ/memo! : (U 'hv-res 'hv-ref 'hv-ap 'opq-ap 'ac-ap 'vref) Any * → -ℓ)
  (define (+ℓ/memo! tag . xs)
    (define ℓ (hash-ref! m (cons tag xs) +ℓ!))
    (hash-set! m⁻¹ ℓ (cons tag xs))
    ℓ)

  (: +ℓ/ctc : -ℓ Natural → -ℓ)
  (define (+ℓ/ctc ℓ i)
    (define ℓₐ (hash-ref! m (list ℓ i) +ℓ!))
    (hash-set! m⁻¹ ℓₐ (list ℓ i))
    ℓₐ)

  (: ℓ⁻¹ : -ℓ → Any)
  ;; Just for debugging
  (define (ℓ⁻¹ ℓ)
    (hash-ref m⁻¹ ℓ (λ () (error 'ℓ⁻¹ "nothing for ~a" ℓ))))
)

(define +ℓ₀ (+ℓ 0))

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

(-provide-spec . ::= . (-p/c-item [id : Symbol] [spec : -e] [loc : -ℓ]))

(-require-spec . ::= . -l #|TODO|#)

(-e . ::= . -v
            (-x Symbol) ; lexical variables 
            -𝒾 ; module references
            (-@ -e (Listof -e) -ℓ)
            (-if -e -e -e)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e])
            (-letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e])
            (-set! (U -𝒾 -x) -e)
            (-error String)
            (-amb (℘ -e))
            
            ;; contract stuff
            (-μ/c Symbol -e)
            (--> [doms : (Listof -e)] [rng : -e] [pos : -ℓ])
            (-->i [doms : (Listof -e)] [rng : -λ] [pos : -ℓ])
            (-case-> [clauses : (Listof (Pairof (Listof -e) -e))] -ℓ)
            (-x/c.tmp Symbol) ; hack
            (-x/c Symbol)
            (-struct/c [name : -𝒾] [fields : (Listof -e)] [pos : -ℓ])

            ;; internal use only
            (-ar -e -e))

(-v . ::= . -prim
            (-λ -formals -e)
            (-case-λ (Listof (Pairof (Listof Symbol) -e)))
            (-• Natural))

(-prim . ::= . ;; Represent *unsafe* operations without contract checks. 
               ;; User code shouldn't have direct access to these.
               ;; Generated `prim` module exports these operations wrapped in contract. -o (-b Base)
               -o
               ;; primitive values that can appear in syntax
               (-b [unboxed : Base]))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))
(define -void (-b (void)))
(define -undefined (-b undefined))

(define -𝒾-values (-𝒾 'values 'Λ))
(define -𝒾-cons (-𝒾 'cons 'Λ))
(define -cons (-st-mk -𝒾-cons))
(define -car (-st-ac -𝒾-cons 0))
(define -cdr (-st-ac -𝒾-cons 1))
(define -cons? (-st-p -𝒾-cons))

(define -zero (-b 0))
(define -one (-b 1))

(define -𝒾-box (-𝒾 'box 'Λ))
(define -box? (-st-p -𝒾-box))
(define -unbox (-st-ac -𝒾-box 0))
(define -box (-st-mk -𝒾-box))
(define -set-box! (-st-mut -𝒾-box 0))
(define -pred (--> (list 'any/c) 'boolean? +ℓ₀))

(define havoc-path 'havoc)
(define havoc-𝒾 (-𝒾 'havoc-id havoc-path))

(: -cond : (Listof (Pairof -e -e)) -e → -e)
;; Make `cond` at object language level, expanding to `if`
(define (-cond cases default)
  (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
           (match-define (cons cnd thn) alt)
           (-if cnd thn els))
         default
         cases))

(: -->* : (Listof -e) -e -e → -e)
;; Make a non-dependent vararg contract
;; TODO: separate case for non-dependent varargs
(define (-->* cs rst d)
  (define xs (-varargs (map (λ (_) (+x!)) cs) (+x!)))
  (-->i (append cs (list rst)) (-λ xs d) (+ℓ!)))

;; Make conjunctive and disjunctive contracts
(splicing-local
    ((: -app/c : Symbol → (Listof -e) → -e)
     (define ((-app/c o) es)
       (let go ([es : (Listof -e) es])
         (match es
           ['() 'any/c]
           [(list e) e]
           [(cons e es*) (-@ o (list e (go es*)) (+ℓ!))]))))
  (define -and/c (-app/c 'and/c))
  (define -or/c (-app/c 'or/c)))

(: -one-of/c : (Listof -e) → -e)
(define (-one-of/c es)
  (cond
    [(null? es) 'none/c]
    [else
     (define x (+x!))
     (define 𝐱 (-x x))
     (define body : -e
       (let build-body ([es : (Listof -e) es])
         (match es
           [(list e) (-@ 'equal? (list 𝐱 e) (+ℓ!))]
           [(cons e es*)
            (-if (-@ 'equal? (list 𝐱 e) (+ℓ!))
                 -tt
                 (build-body es*))])))
     (-λ (list x) body)]))

(: -cons/c : -e -e → -e)
(define (-cons/c c d)
  (-struct/c -𝒾-cons (list c d) (+ℓ!)))

(: -listof : -e → -e)
(define (-listof c)
  (define x (+x! 'rec))
  (-μ/c x (-or/c (list 'null? (-cons/c c (-x/c x))))))

(: -box/c : -e → -e)
(define (-box/c c)
  (-struct/c -𝒾-box (list c) (+ℓ!)))

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

(define (show-ℓ [ℓ : -ℓ]) : Symbol
  (format-symbol "ℓ~a" (n-sub ℓ)))

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
   [(== -car) 'car]
   [(== -cdr) 'cdr]
   [(== -unbox) 'unbox]
   [(-st-ac 𝒾 i) (format-symbol "~a@~a" (-𝒾-name 𝒾) i)]
   [(-st-p 𝒾) (format-symbol "~a?" (-𝒾-name 𝒾))]
   [(== -set-box!) 'set-box!]
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
    [(-• i) (format-symbol "•~a" (n-sub i))]
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
    [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (show-e e)))]
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

(define (show-e-map [m : (HashTable -e -e)]) : (Listof Sexp)
  (for/list ([(x y) m]) `(,(show-e x) ↦ ,(show-e y))))
