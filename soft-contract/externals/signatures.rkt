#lang typed/racket/base

(require typed/racket/unit
         "../runtime/main.rkt")

(define-signature ext-runtime^
  ([ext-table : (HashTable Symbol -⟦f⟧)]))
