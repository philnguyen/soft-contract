#lang typed/racket/base

(provide prims-04-06@)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.6 Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-06@
  (import prim-runtime^ proof-system^ widening^)
  (export)


  (def-pred symbol?)
  (def-pred symbol-interned? (symbol?))
  (def-pred symbol-unreadable? (symbol?))
  (def-prim symbol->string
    (symbol? . -> . string?))
  (def-prims (string->symbol string->uninterned-symbol string->unreadable-symbol)
    (string? . -> . symbol?))
  (def-prim gensym (-> symbol?)) ; FIXME use
  (def-pred symbol<? (symbol? symbol?))
  
  )
