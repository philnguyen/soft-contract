#lang typed/racket/base

(require typed/racket/unit
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "def.rkt")

(provide prims-11@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Concurrency and Parallelism
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-11@
  (import prim-runtime^
          sto^
          exec^)
  (export)

  ;; 11.3.1 Thread Cells
  (def-pred thread-cell?)
  (def-alias-internal make-thread-cell -thread-cell) ; FIXME uses
  (def-alias-internal thread-cell-ref -thread-cell-ref)
  (def-alias-internal thread-cell-set! -set-thread-cell!)

  ;; 11.3.2 Parameters
  (def (make-parameter Σ ℓ W)
    #:init ([V any/c])
    (define α (α:dyn (β:param ℓ) H₀))
    (just (Param α) (alloc α V)))
)
