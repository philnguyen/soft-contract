#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-17@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.17 Procedures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-17@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  (def-pred procedure?)
  #;[apply ; FIXME uses. This probably should be treated specially for precision ; FIXME listof
     (procedure? (listof any/c) . -> . any)]
  (def-prim/todo compose ; FIXME uses
    ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
  (def-prim/todo compose1 ; FIXME uses
    ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
  (def-prim/todo procedure-rename
    (procedure? symbol? . -> . procedure?))
  (def-prim/todo procedure->method
    (procedure? . -> . procedure?))
  (def-pred procedure-closure-contents-eq? (procedure? procedure?))

  ;; 4.17.1 Keywords and Arity
  ;[keyword-apply #|FIXME uses|#]
  (def-prim/custom (procedure-arity ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W procedure?])
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'procedure-arity s))
    (cond [(V-arity V) => (λ ([a : Arity]) {set (-ΓA (-Γ-facts Γ) (-W (list (-b a)) sₐ))})]
          [else {set (-ΓA (-Γ-facts Γ) (-W -●.Vs sₐ))}]))
  (def-pred procedure-arity?)
  {def-pred procedure-arity-includes? (procedure? exact-nonnegative-integer?)} ; FIXME uses
  (def-prim/todo procedure-reduce-arity
    (procedure? procedure-arity? . -> . procedure?))
  #;[procedure-keywords ; FIXME listof
     (procedure? . -> . (values (listof keyword?) (or/c (listof keyword?) not)))]
  #;[make-keyword-procedure ; FIXME uses
     ((((listof keyword?) list?) () #:rest list? . ->* . any) . -> . procedure?)]
  #;[procedure-reduce-keyword-arity ; FIXME listof
     (procedure? procedure-arity? (listof keyword?) (or/c (listof keyword?) not)
                 . -> . procedure?)]
  (def-pred arity-at-least?)
  (def-prim/todo arity-at-least (exact-nonnegative-integer? . -> . arity-at-least?))
  (def-prim/todo arity-at-least-value (arity-at-least? . -> . exact-nonnegative-integer?))
  (def-alias make-arity-at-least arity-at-least)
  (def-opq prop:procedure struct-type-property?)
  [def-pred procedure-struct-type? (struct-type?)]
  (def-prim/todo procedure-extract-target
    (procedure? . -> . (or/c procedure? not)))
  (def-opq prop:arity-string struct-type-property?)
  (def-opq prop:checked-procedure struct-type-property?)
  (def-prim/todo checked-procedure-check-and-extract
    (struct-type? any/c (any/c any/c any/c . -> . any/c) any/c any/c . -> . any/c))

  ;; 4.17.2 Reflecting on Primitives
  (def-pred primitive?)
  (def-pred primitive-closure?)
  (def-prim/todo primitive-result-arity
    (primitive? . -> . procedure-arity?))

  ;; 4.17.3 Additional Higher-Order Functions
  (def-prim/custom (identity ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W any/c])
    (match-define (-W¹ V s) W)
    {set (-ΓA (-Γ-facts Γ) (-W (list V) s))})
  (def-prim/todo const (any . -> . procedure?))
  (def-prim/todo negate (procedure? . -> . procedure?))
  ;[curry ] FIXME
  ;[curryr] FIXME
  (def-pred/todo normalized-arity?)
  (def-prim/todo normalize-arity ; FIXME dependency
    (procedure-arity? . -> . normalized-arity?))
  (def-pred arity=? (procedure-arity? procedure-arity?))
  (def-pred arity-includes? (procedure-arity? procedure-arity?))
  
  )
