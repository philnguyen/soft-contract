#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "../utils/def.rkt" "../utils/pretty.rkt")

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
(define-data -id
  ;; primitive ids as symbols to ease notation
  'cons 'box 'μ/c 'x/c
  ;; these are just (tmp) hacks for retaining expressions / allocation address
  'values 'vector
  ;; general user-defined id
  (struct -id-local [name : Symbol] [ctx : Adhoc-Module-Path]))

(define (-id-name [id : -id]) : Symbol
  (cond [(symbol? id) id]
        [else (-id-local-name id)]))

;; Struct meta data
(struct -struct-info ([id : -id] [arity : Integer] [mutables : (Setof Integer)]) #:transparent)

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
  (U Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Char Null Void))

(define-data -top-level-form
  -general-top-level-form
  -e
  -module
  -begin/top)

(define-data -module-level-form
  -general-top-level-form
  (struct -provide [specs : (Listof -provide-spec)])
  -submodule-form)

(define-data -general-top-level-form
  -e
  (struct -define-values [ids : (Listof Symbol)] [e : -e])
  (struct -require [specs : (Listof -require-spec)]))

(define-data -submodule-form
  (struct -module [path : Adhoc-Module-Path] [body : -plain-module-begin]))

(define-data -provide-spec
  (struct -p/c-item [id : Symbol] [spec : -e] #|TODO|#))

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
  (struct -μ/c [x : Symbol] [c : -e] [pos : Integer])
  (struct -->i [dom : (Listof (Pairof Symbol -e))] [rng : -e] [pos : Integer])
  (struct -x/c [x : Symbol])
  (struct -struct/c [info : -struct-info] [fields : (Listof -e)] [pos : Integer]))

(define-type -es (Setof -e))

;; Current restricted representation of program
(struct -prog ([modules : (Listof -module)] [main : -e]) #:transparent)
