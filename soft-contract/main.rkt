#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "verifier.rkt"
         "proof-relation/main.rkt"
         "reduction/main.rkt"
         "primitives/main.rkt"
         "parse/main.rkt"
         "primitives/signatures.rkt"
         "signatures.rkt"
         )

(define-values/invoke-unit/infer
  (export verifier^ parser^ prim-runtime^)
  (link prims@ proof-system@ reduction@ verifier@ parser@))
