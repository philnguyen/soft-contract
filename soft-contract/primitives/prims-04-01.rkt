#lang typed/racket/base

(provide prims-04-01@)

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
;;;;; 4.1 Booleans and Equality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-01@
  (import prim-runtime^)
  (export)

  (def-pred boolean?)
  (def-pred not)

  (def-preds (equal? eqv? eq?) (any/c any/c))
  ; [HO] equal?/recur
  (def-pred immutable?)
  (def-opq prop:equal+hash any/c)

  (def-const true)
  (def-const false)
  (def-pred symbol=? (symbol? symbol?))
  (def-pred boolean=? (boolean? boolean?))
  (def-alias false? not)
  (def xor (any/c any/c . -> . any/c))
  )
