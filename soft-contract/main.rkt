#lang typed/racket/base

(require typed/racket/unit
         "verifier.rkt"
         "proof-relation/main.rkt"
         "reduction/main.rkt"
         "primitives/main.rkt"
         "externals/main.rkt"
         "signatures.rkt"
         )

(define-compound-unit/infer main@
  (import parser^)
  (export verifier^)
  (link prims@ exts@ proof-system@ reduction@ verifier@))
