#lang typed/racket/base

(provide exts@)

(require typed/racket/unit
         "../runtime/main.rkt"
         "ext-runtime.rkt"
         "exts-04.rkt"
         "exts-10.rkt"
         "exts-13.rkt"
         "exts-17.rkt"
         "../reduction/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit pre-exts@
  (import ext-runtime^)
  (export exts^)
  
  (: get-ext : Symbol → (Option -⟦f⟧))
  (define (get-ext o)
    (printf "exts: ~a~n" (hash-keys ext-table))
    (hash-ref ext-table o #f)))

(define-compound-unit/infer exts@
  (import #;prim-runtime^ proof-system^ widening^ app^ mon^ kont^ compile^)
  (export exts^ ext-runtime^)
  (link ext-runtime@
        pre-exts@
        exts-04@
        exts-10@
        exts-13@
        exts-17@
        ))

