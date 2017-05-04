#lang typed/racket/base

(provide exts@)

(require "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit pre-exts@
  (import ext-runtime^)
  (export exts^)
  
  (: get-ext : Symbol → (Option -⟦f⟧))
  (define (get-ext o) (hash-ref ext-table o #f)))

(define-compound-unit/infer exts@
  (import proof-system^ widening^)
  (export exts^)
  (link pre-exts@ ; TODO
        ))

