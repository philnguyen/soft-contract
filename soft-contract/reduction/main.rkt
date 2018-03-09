#lang typed/racket/base

(provide reduction@)

(require typed/racket/unit
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "alloc.rkt"
         "reflection.rkt"
         "mon.rkt"
         "app.rkt"
         "compile.rkt"
         "step.rkt"
         )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          env^ val^ sto^ evl^
          proof-system^)
  (export compile^ step^)
  (link alloc@ reflection@ app@ mon@ compile@ step@))

