#lang typed/racket/base

(provide prims-17@)

(require racket/contract
         typed/racket/unit
         "def-prim.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-17@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Data Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-alias unsafe-car car)
  (def-alias unsafe-cdr cdr)
  (def-alias unsafe-vector-length vector-length)
  (def-alias unsafe-vector-ref vector-ref)
  (def-alias unsafe-vector-set! vector-set!))

