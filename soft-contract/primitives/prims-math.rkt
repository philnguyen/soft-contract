#lang typed/racket/base

(provide prims-math@)

(require racket/contract
         typed/racket/unit
         "def-prim.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-math@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; FROM THE MATH LIBRARY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 1.2 Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-pred float-complex?)
  )
