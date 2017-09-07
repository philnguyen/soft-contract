#lang typed/racket/base

(provide prims-16@)
(require racket/contract
         typed/racket/unit
         "def.rkt"
         "signatures.rkt")

(define-unit prims-16@
  (import prim-runtime^)
  (export)
  
  (def make-weak-box (any/c . -> . weak-box?))
  (def weak-box-value
    (case->
     [weak-box? . -> . any/c]
     [weak-box? any/c . -> . any/c]))
  (def-pred weak-box?))
