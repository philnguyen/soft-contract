#lang typed/racket/base

(provide prims-14@)

(require racket/contract
         typed/racket/unit
         racket/path
         "def.rkt"
         "signatures.rkt")

(define-unit prims-14@
  (import prim-runtime^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 14.4 Module Names and Loading
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; 14.4.2 Compiled Modules and References
  (def-pred module-path-index?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 14.5 Impersonators and Chaperones
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-pred impersonator?)
  
  )

