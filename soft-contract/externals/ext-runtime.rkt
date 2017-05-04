#lang typed/racket/base

(provide ext-runtime@)

(require typed/racket/unit
         "../runtime/definition.rkt"
         )

(define-unit ext-runtime@
  (import)
  (export ext-runtime^)
  (define ext-table : (HashTable Symbol -⟦f⟧) (make-hasheq)))
