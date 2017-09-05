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
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.12 Boxes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide prims-04-12@)

(define-unit prims-04-12@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)
  
  (def-alias-internal box? -box?)
  (def-alias-internal box -box)
  (def-alias-internal unbox -unbox)
  (def-alias-internal set-box! -set-box!)
  )
  
