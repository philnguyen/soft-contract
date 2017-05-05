#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "verifier.rkt"
         "proof-relation/main.rkt"
         "reduction/main.rkt"
         "primitives/main.rkt"
         "externals/main.rkt"
         "parse/main.rkt"
         "signatures.rkt"
         )

(define-values/invoke-unit/infer
  (export verifier^ parser^)
  (link prims@ exts@ proof-system@ reduction@ verifier@ parser@))
