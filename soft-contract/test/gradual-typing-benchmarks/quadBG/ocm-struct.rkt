#lang racket/base

(provide
  (struct-out $ocm)
  set-$ocm-tentative!
  set-$ocm-min-entrys!
  set-$ocm-min-row-indices!
  set-$ocm-finished!
  set-$ocm-base!
)

;; =============================================================================

(struct $ocm (
  min-entrys ;: (Vectorof Entry-Type)]
  min-row-indices ;: (Vectorof (U Index-Type No-Value-Type))]
  finished ;: Finished-Value-Type]
  matrix-proc ;: Matrix-Proc-Type]
  entry->value ;: Entry->Value-Type]
  base ;: Index-Type]
  tentative ;: Index-Type]
) #:transparent #:mutable)

;; -----------------------------------------------------------------------------

;(define-type Index-Type Nonnegative-Integer)
;(define-type Entry-Type Any)
;(define-type Value-Type Float)
;(define-type No-Value-Type Symbol)
;(define-type Finished-Value-Type Index-Type)
;(define-type Matrix-Proc-Type (Index-Type Index-Type -> Entry-Type))
;(define-type Entry->Value-Type (Entry-Type -> Value-Type))


