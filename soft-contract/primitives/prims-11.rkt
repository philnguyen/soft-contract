#lang typed/racket/base

(require typed/racket/unit
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt")

(provide prims-11@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Concurrency and Parallelism
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-11@
  (import prim-runtime^)
  (export)

  ;; 11.3.1 Thread Cells
  (def-pred thread-cell?)
  (def-alias-internal make-thread-cell -thread-cell) ; FIXME uses
  (def-alias-internal thread-cell-ref -thread-cell-ref)
  (def-alias-internal thread-cell-set! -set-thread-cell!)
)
