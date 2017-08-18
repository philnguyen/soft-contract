#lang typed/racket/base

(provide (all-defined-out)
         (all-from-out "arity.rkt" "srcloc.rkt"))

(require racket/match
         racket/set
         racket/list
         racket/string
         racket/extflonum 
         racket/splicing
         typed/racket/unit
         bnf
         set-extras
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
(struct -𝒾 ([name : Symbol] [src : -l]) #:transparent)

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
            (-x (U Symbol -𝒾) ℓ) ; lexical/module ref
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

(define -cons (-st-mk -𝒾-cons))
(define -car (-st-ac -𝒾-cons 0))
(define -cdr (-st-ac -𝒾-cons 1))
(define -set-cdr! (-st-mut -𝒾-cons 1)) ; HACK for running some scheme programs
(define -cons? (-st-p -𝒾-cons))

(define -mcons (-st-mk -𝒾-mcons))
(define -mcar (-st-ac -𝒾-mcons 0))
(define -mcdr (-st-ac -𝒾-mcons 1))
(define -set-mcar! (-st-mut -𝒾-mcons 0))
(define -set-mcdr! (-st-mut -𝒾-mcons 1))
(define -mpair? (-st-p -𝒾-mcons))

(define -zero (-b 0))
(define -one (-b 1))

(define -box? (-st-p -𝒾-box))
(define -unbox (-st-ac -𝒾-box 0))
(define -box (-st-mk -𝒾-box))
(define -set-box! (-st-mut -𝒾-box 0))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty Printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-signature ast-pretty-print^
  ([show-b : (Base → Sexp)]
   [show-o : (-o → Symbol)]
   [show-ac : (-𝒾 Index → Symbol)]
   [show-e : (-e → Sexp)]
   [show-es : ((Sequenceof -e) → (Listof Sexp))]
   [show-module : (-module → (Listof Sexp))]
   [show-module-level-form : (-module-level-form → Sexp)]
   [show-general-top-level-form : (-general-top-level-form → Sexp)]
   [show-provide-spec : (-provide-spec → Sexp)]
   [show-require-spec : (-require-spec → Sexp)]
   [show-formals : (-formals → Sexp)]
   [show-𝒾 : (-𝒾 → Sexp)]
   [show-values-lift : (∀ (X) (X → Sexp) → (Listof X) → Sexp)]
   [show-values : ((Listof -e) → Sexp)]
   [show-subst : (Subst → (Listof Sexp))]
   ))

(define-signature ast-macros^
  ([-define : (Symbol -e → -define-values)]
   [-cond : ((Listof (Pairof -e -e)) -e → -e)]
   [-cons/c : (-e -e ℓ → -e)]
   [-box/c : (-e ℓ → -e)]
   [-list/c : ((Listof (Pairof ℓ -e)) → -e)]
   [-list : ((Listof (Pairof ℓ -e)) → -e)]
   [-and : (-e * → -e)]
   [-comp/c : (Symbol -e ℓ → -e)]
   [-begin/simp : (∀ (X) (Listof X) → (U X (-begin X)))]
   [-begin0/simp : (-e (Listof -e) → -e)]
   [-@/simp : (-e (Listof -e) ℓ → -e)]
   [-let-values/simp : ((Listof (Pairof (Listof Symbol) -e)) -e ℓ → -e)]
   [-if/simp : (-e -e -e → -e)]))

(define-signature meta-functions^
  ([fv : (-e → (℘ Symbol))]
   [bv : (-e → (℘ Symbol))]
   [closed? : (-e → Boolean)]
   [free-x/c : (-e → (℘ Symbol))]
   [e/map : (Subst -e → -e)]
   [e/ : (Symbol -e -e → -e)]
   [formals->names : (-formals → (℘ Symbol))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; program-dependent static info
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-new-subtype -struct-info (Vector->struct-info (Vectorof Boolean)))
(struct -static-info ([structs : (HashTable -𝒾 -struct-info)]
                      [public-accs : (HashTable -𝒾 (℘ -st-ac))]
                      [public-muts : (HashTable -𝒾 (℘ -st-mut))]
                      [top-level-defs : (HashTable -𝒾 #t)]
                      [export-aliases : (HashTable -𝒾 -𝒾)]
                      [dependencies : (HashTable -l (℘ -l))]
                      [alternate-aliases : (HashTable -𝒾 (Pairof -𝒾 Boolean))]
                      [alternate-alias-ids : (HashTable -l Symbol)]
                      [assignables : (HashTable (U Symbol -𝒾) #t)]
                      [parentstruct : (HashTable -𝒾 -𝒾)])
  #:transparent)

(define-signature static-info^
  ([new-static-info : (→ -static-info)]
   [current-static-info : (Parameterof -static-info)]
   [count-direct-struct-fields : (-𝒾 → Index)]
   [struct-all-immutable? : (-𝒾 → Boolean)]
   [struct-mutable? : (-𝒾 Index → Boolean)]
   [add-struct-info! : (-𝒾 Index (℘ Index) → Void)]
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
   [set-parent-struct! : (-𝒾 -𝒾 → Void)]
   [substruct? : (-𝒾 -𝒾 → Boolean)]
   [field-offset : (-𝒾 → Index)]
   [count-struct-fields : (-𝒾 → Index)]))
