#lang typed/racket/base

(provide prims-04@)

(require typed/racket/unit
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "prims-04-01.rkt"
         "prims-04-02.rkt"
         "prims-04-03.rkt"
         "prims-04-04.rkt"
         "prims-04-05.rkt"
         "prims-04-06.rkt"
         "prims-04-07.rkt"
         "prims-04-08.rkt"
         "prims-04-09.rkt"
         "prims-04-10.rkt"
         "prims-04-11.rkt"
         "prims-04-12.rkt"
         "prims-04-13.rkt"
         "prims-04-14.rkt"
         "prims-04-15.rkt"
         "prims-04-16.rkt"
         "prims-04-17.rkt"
         "prims-04-18.rkt"
         "prims-04-19.rkt"
         )

(define-compound-unit/infer prims-04@
  (import prim-runtime^ evl^ val^ sto^
          prover^
          mon^ step^ approx^ app^)
  (export)
  (link prims-04-01@
        prims-04-02@
        prims-04-03@
        prims-04-04@
        prims-04-05@
        prims-04-06@
        prims-04-07@
        prims-04-08@
        prims-04-09@
        prims-04-10@
        prims-04-11@
        prims-04-12@
        prims-04-13@
        prims-04-14@
        prims-04-15@
        prims-04-16@
        prims-04-17@
        prims-04-18@
        prims-04-19@
        ))
