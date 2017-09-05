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
;;;;; 4.10 Mutable Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide prims-04-10@)

(define-unit prims-04-10@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)

  #|(def-alias-internal mpair? -mpair?)
  (def-alias-internal mcons -mcons)
  (def-alias-internal mcar -mcar)
  (def-alias-internal mcdr -mcdr)
  (def-alias-internal set-mcar! -set-mcar!)
  (def-alias-internal set-mcdr! -set-mcdr!)|#
  )
