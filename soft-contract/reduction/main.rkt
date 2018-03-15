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
         "fc.rkt"
         "app.rkt"
         "compile.rkt"
         "step.rkt"
         )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          env^ val^ sto^ evl^
          prims^ proof-system^)
  (export reflection^ alloc^ app^ mon^ compile^ step^)
  (link reflection@ alloc@ fc@ mon@ compile@ step@ app@))
