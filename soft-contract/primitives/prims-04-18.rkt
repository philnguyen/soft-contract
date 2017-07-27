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
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-18@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.18 Void
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-18@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)

  (def-pred void?)
  (def-prim/custom (void ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    {set (-ΓA Γ (+W (list -void)))})
  )
