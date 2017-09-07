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
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.6 Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-06@
  (import prim-runtime^)
  (export)


  (def-pred symbol?)
  (def-pred symbol-interned? (symbol?))
  (def-pred symbol-unreadable? (symbol?))
  (def symbol->string
    (symbol? . -> . string?))
  (def* (string->symbol string->uninterned-symbol string->unreadable-symbol)
    (string? . -> . symbol?))
  (def gensym
    (case->
     [-> symbol?]
     [(or/c string? symbol?) . -> . symbol?]))
  (def-pred symbol<? (symbol? symbol?))
  
  )
