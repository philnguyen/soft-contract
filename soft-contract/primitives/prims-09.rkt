#lang typed/racket/base

(provide prims-09@)

(require racket/match
         racket/set
         racket/contract
         racket/splicing
         typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "def-prim.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-09@
  (import prim-runtime^ proof-system^ widening^ app^ kont^ val^ pc^ sto^ instr^ env^)
  (export)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; 9.2 Extending match
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-ext match-equality-test (-> (any/c any/c . -> . any/c))) ; FIXME parameter

  )
