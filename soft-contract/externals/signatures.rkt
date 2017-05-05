#lang typed/racket/base

(provide ext-runtime^ ext-for-parser^)

(require typed/racket/unit
         set-extras
         "../runtime/main.rkt")

(define-signature ext-runtime^
  ([ext-table : (HashTable Symbol -⟦f⟧)]))

(define-signature ext-for-parser^
  ([get-defined-ext-names : (→ (℘ Symbol))]
   [get-ext-parse-result : (Symbol → (Values (U 'quote 'const) Symbol))]))
