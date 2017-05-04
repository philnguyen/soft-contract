#lang typed/racket/base

(provide prims-16@)
(require racket/contract
         typed/racket/unit
         "def-prim.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-16@
  (import prim-runtime^ proof-system^ widening^)
  (export)
  
  (def-prim make-weak-box (any/c . -> . weak-box?))
  (def-prim weak-box-value (weak-box? . -> . any/c)) ; FIXME uses
  (def-pred weak-box?))
