#lang typed/racket/base

(provide prims-09@)

(require racket/match
         racket/set
         racket/contract
         racket/splicing
         typed/racket/unit
         set-extras
         "def.rkt"
         "signatures.rkt")

(define-unit prims-09@
  (import prim-runtime^)
  (export)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; 9.2 Extending match
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def match-equality-test (-> (any/c any/c . -> . any/c))) ; FIXME parameter

  )
