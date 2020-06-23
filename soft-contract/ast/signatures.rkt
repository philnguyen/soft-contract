#lang typed/racket/base

(provide (all-defined-out)
         (all-from-out "arity.rkt" "srcloc.rkt"))

(require (for-syntax racket/base
                     racket/syntax
                     racket/pretty)
         racket/match
         racket/set
         racket/list
         racket/extflonum 
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         bnf
         set-extras
         "../utils/pretty.rkt"
         "../utils/list.rkt"
         "arity.rkt"
         "srcloc.rkt")

(require/typed/provide racket/undefined
  [undefined Undefined])

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

(struct (X) -var ([init : (Listof X)] [rest : (Option X)]) #:transparent) 

;; Identifier as a name and its source
(struct -𝒾 ([name : Symbol] [src : -l]) #:transparent)

;; Formal parameters
(-formals . ::= . [#:reuse (-var Symbol)])

(Binding . ≜ . (Binding [lhs : (Listof Symbol)] [rhs : -e]) #:ad-hoc)

(Base . ::= . Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Byte-Regexp Byte-PRegexp Char Null Void Arity EOF Undefined Path)

(-dom . ::= . (-dom [name : Symbol] [dependency : (Option (Listof Symbol))] [body : -e] [loc : ℓ]))

(-prog . ::= . (-prog (Listof -module)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(-top-level-form . ::= . -general-top-level-form
                         -e
                         -module
                         -begin/top)

(-module-level-form . ::= . -general-top-level-form
                            (-provide [specs : (Listof -provide-spec)])
                            -submodule-form)

(-general-top-level-form . ::= . -e
                                 (-define-values [ids : (Listof Symbol)] [e : -e] ℓ)
                                 (-require (Listof -require-spec)))

(-submodule-form . ::= . (-module [path : -l] [body : (Listof -module-level-form)]))

(-provide-spec . ::= . (-p/c-item [id : (U -𝒾 -o)] [spec : -e] [loc : ℓ])
                       -𝒾
                       -o)

(-require-spec . ::= . -l #|TODO|#)

(-e . ::= . -v
            (-x (U Symbol -𝒾) ℓ) ; lexical/module ref
            (-@ -e (Listof -e) ℓ)
            (-if -e -e -e ℓ)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof Binding)]
                         [body : -e]
                         [loc : ℓ])
            (-letrec-values [bnds : (Listof Binding)]
                            [body : -e]
                            [loc : ℓ])
            (-set! (U Symbol -𝒾) -e ℓ)
            (-error String ℓ)
            (-parameterize (Listof (Pairof -e -e)) -e ℓ)
            
            ;; contract stuff
            (-rec/c -x)
            (-->i [doms : (-var -dom)] [rng : (Option (Listof -dom))])
            (case--> [cases : (Listof -->i)])
            (-∀/c (Listof Symbol) -e ℓ)
            )

(-v . ::= . -prim
            (-λ -formals -e ℓ)
            (-case-λ (Listof -λ) ℓ)
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

(define-syntax-parser dec-prim-struct
  [(_ st:id fld:id ... #:mutable? mut:boolean)
   (with-syntax* ([-𝒾-name (format-id #'st "-𝒾-~a" #'st)]
                  [-st (format-id #'st "-~a" #'st)]
                  [-st? (format-id #'st "-~a?" #'st)]
                  [(def-ac ...)
                   (for/list ([f (in-list (syntax->list #'(fld ...)))]
                              [i (in-naturals)])
                     #`(define #,(format-id #'st "-~a" f) (-st-ac -𝒾-name #,i)))]
                  [(def-set ...)
                   (cond
                     [(not (syntax-e #'mut))
                      '()]
                     [(= 1 (length (syntax->list #'(fld ...))))
                      #`((define #,(format-id #'st "-set-~a!" #'st) (-st-mut -𝒾-name 0)))]
                     [else
                      (for/list ([f (in-list (syntax->list #'(fld ...)))]
                                 [i (in-naturals)])
                        #`(define #,(format-id #'st "-set-~a!" f) (-st-mut -𝒾-name #,i)))])])
     #'(begin
         (define -𝒾-name (-𝒾 'st 'Λ))
         (define -st (-st-mk -𝒾-name))
         (define -st? (-st-p -𝒾-name))
         def-ac ...
         def-set ...))])

(dec-prim-struct cons car cdr #:mutable? #f)
(dec-prim-struct mcons mcar mcdr #:mutable? #t)
(dec-prim-struct box unbox #:mutable? #t)
(dec-prim-struct thread-cell thread-cell-ref #:mutable? #t)

;; FIXME: HACKS for Scheme programs
(define -set-car! (-st-mut -𝒾-cons 0))
(define -set-cdr! (-st-mut -𝒾-cons 1))

(define-type Subst (Immutable-HashTable Symbol -e))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))
(define -void (-b (void)))
(define -null-char (-b #\null))
(define -undefined (-b undefined))

(define -zero (-b 0))
(define -one (-b 1))

(: var-map (∀ (X Y) (X → Y) (-var X) → (-var Y)))
(define (var-map f v)
  (match-define (-var xs x) v)
  (-var (map f xs) (and x (f x))))

(: var->set (∀ (X) ([(-var X)] [#:eq? Boolean] . ->* . (℘ X))))
(define (var->set xs #:eq? [use-eq? #f])
  (match-define (-var xs₀ ?xᵣ) xs)
  (define s ((if use-eq? list->seteq list->set) xs₀))
  (if ?xᵣ (set-add s ?xᵣ) s))

(: var-fold (∀ (X Y Z) (X Y Z → Z) Z (-var X) (-var Y) → Z))
(define (var-fold f z₀ xs ys)
  (match-define (-var xs₀ ?xᵣ) xs)
  (match-define (-var ys₀ ?yᵣ) ys)
  (define z₁ (foldl f z₀ xs₀ ys₀))
  (if (and ?xᵣ ?yᵣ) (f ?xᵣ ?yᵣ z₁) z₁))

(: in-var (∀ (X) (-var X) → (Sequenceof X)))
(define in-var
  (match-lambda
    [(-var xs ?x) (cond [?x (in-sequences (in-list xs) (in-value ?x))]
                        [else (in-list xs)])]))

(: shape (∀ (X) (-var X) → (U Index arity-at-least)))
(define shape
  (match-lambda
    [(-var (app length n) x) (if x (arity-at-least n) n)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty Printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-signature ast-pretty-print^
  ([show-b : (Base → Sexp)]
   [show-o : (-o → Symbol)]
   [show-e : (-e → Sexp)]
   [show-es : ((Sequenceof -e) → (Listof Sexp))]
   [show-module : (-module → (Listof Sexp))]
   [show-module-level-form : (-module-level-form → Sexp)]
   [show-general-top-level-form : (-general-top-level-form → Sexp)]
   [show-provide-spec : (-provide-spec → Sexp)]
   [show-require-spec : (-require-spec → Sexp)]
   [show-formals : (-formals → Sexp)]
   [show-𝒾 : (-𝒾 → String)]
   [show-values-lift : (∀ (X) (X → Sexp) → (Listof X) → Sexp)]
   [show-values : ((Listof -e) → Sexp)]
   [show-subst : (Subst → (Listof Sexp))]
   ))

(define-signature ast-macros^
  ([-define : (Symbol -e ℓ → -define-values)]
   [-cond : ((Assoc -e -e) -e ℓ → -e)]
   [--> : ((-var -e) -e ℓ → -->i)]
   [-cons/c : (-e -e ℓ → -e)]
   [-box/c : (-e ℓ → -e)]
   [-list/c : ((Assoc ℓ -e) → -e)]
   [-list : ((Assoc ℓ -e) → -e)]
   [-and : ((Listof -e) ℓ → -e)]
   [-comp/c : (Symbol -e ℓ → -e)]
   [-begin/simp : (∀ (X) (Listof X) → (U X (-begin X)))]
   [-begin0/simp : (-e (Listof -e) → -e)]
   [-@/simp : (-e (Listof -e) ℓ → -e)]
   [-let-values/simp : ((Listof Binding) -e ℓ → -e)]
   [-if/simp : (-e -e -e ℓ → -e)]))

(define-signature meta-functions^
  ([fv : (-e → (℘ Symbol))]
   [fv-count : (-e Symbol → Natural)]
   [e/map : (Subst -e → -e)]
   [e/ : (Symbol -e -e → -e)]
   [formals->names : ([-formals] [#:eq? Boolean] . ->* . (℘ Symbol))]
   [first-forward-ref : ((Listof -dom) → (Option Symbol))]
   [+x! : ((U Symbol Integer) * → Symbol)]
   [+x!/memo : ((U Symbol Integer) * → Symbol)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; program-dependent static info
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-new-subtype -struct-info (Vector->struct-info (Immutable-Vectorof (Pairof Symbol Boolean))))
(struct -static-info ([structs : (HashTable -𝒾 -struct-info)]
                      [public-accs : (HashTable -𝒾 (℘ -st-ac))]
                      [public-muts : (HashTable -𝒾 (℘ -st-mut))]
                      [top-level-defs : (HashTable -𝒾 #t)]
                      [export-aliases : (HashTable -𝒾 -𝒾)]
                      [dependencies : (HashTable -l (℘ -l))]
                      [alternate-aliases : (HashTable -𝒾 (Pairof -𝒾 Boolean))]
                      [alternate-alias-ids : (HashTable -l Symbol)]
                      [assignables : (HashTable (U Symbol -𝒾) #t)]
                      [parentstruct : (HashTable -𝒾 -𝒾)]
                      [transparent-modules : (HashTable -l #t)]
                      [struct-alias : (HashTable -𝒾 -𝒾)])
  #:transparent)

(define-signature static-info^
  ([new-static-info : (→ -static-info)]
   [current-static-info : (Parameterof -static-info)]
   [count-direct-struct-fields : (-𝒾 → Index)]
   [struct-all-immutable? : (-𝒾 → Boolean)]
   [struct-mutable? : (-𝒾 Natural → Boolean)]
   [struct-direct-accessor-names : (-𝒾 → (Listof Symbol))]
   [all-struct-accessors : (-𝒾 → (Listof -st-ac))]
   [struct-accessor-name : (-𝒾 Integer → Symbol)]
   [add-struct-info! : (-𝒾 (Listof Symbol) (℘ Natural) → Void)]
   [add-top-level! : (-𝒾 → Void)]
   [top-levels : (→ (Listof -𝒾))]
   [get-public-accs : (-𝒾 → (℘ -st-ac))]
   [get-public-muts : (-𝒾 → (℘ -st-mut))]
   [add-public-acc! : (-𝒾 -st-ac → Void)]
   [add-public-mut! : (-𝒾 -st-mut → Void)]
   [get-export-alias : (∀ (X) ([-𝒾] [(→ X)] . ->* . (U X -𝒾)))]
   [set-export-alias! : (-𝒾 -𝒾 → Void)]
   [get-alternate-alias : (∀ (X) ([-𝒾] [(→ X)] . ->* . (U X (Pairof -𝒾 Boolean))))]
   [set-alternate-alias! : (-𝒾 -𝒾 Boolean → Void)]
   [set-alternate-alias-id! : (-l Symbol → Void)]
   [get-alternate-alias-id : (∀ (X) ([-l] [(→ X)] . ->* . (U X Symbol)))]
   [module-before? : (-l -l → Boolean)]
   [set-module-before! : (-l -l → Void)]
   [assignable? : ((U Symbol -𝒾) → Boolean)]
   [set-assignable! : ((U Symbol -𝒾) → Void)]
   [in-struct-tags : (→ (Sequenceof -𝒾))]
   [set-parent-struct! : (-𝒾 -𝒾 → Void)]
   [substruct? : (-𝒾 -𝒾 → Boolean)]
   [struct-offset : (-𝒾 → Index)]
   [count-struct-fields : (-𝒾 → Index)]
   [add-transparent-module! : (-l → Void)]
   [transparent-module? : (-l → Boolean)]
   [prim-struct? : (-𝒾 → Boolean)]
   [resolve-struct-alias : (-𝒾 → -𝒾)]
   [set-struct-alias! : (-𝒾 -𝒾 → Void)]))
