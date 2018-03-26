#lang typed/racket/base

(provide reduction@)

(require typed/racket/unit
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "alloc.rkt"
         "mon.rkt"
         "fc.rkt"
         "app.rkt"
         "compile.rkt"
         "step.rkt"
         "havoc.rkt"
         )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          env^ val^ sto^ evl^ for-gc^
          prims^ prover^)
  (export alloc^ app^ mon^ compile^ step^)
  (link alloc@ fc@ mon@ compile@ step@ app@ havoc@))
