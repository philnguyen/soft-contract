#lang typed/racket/base

(provide prims-scv@)

(require racket/match
         racket/contract
         typed/racket/unit
         racket/set
         "../utils/debug.rkt"
         "../utils/list.rkt"
         "../utils/patterns.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-scv@
  (import prim-runtime^)
  (export)

  (def (scv:make-case-lambda ℓ Vs H φ Σ ⟦k⟧)
    #:init ()
    #:rest [Vs (listof any/c)]
    (define clos
      (for/list : (Listof -Clo) ([V^ (in-list Vs)])
        (match V^
          [(singleton-set (? -Clo? V)) V]
          [_ (error 'scv:make-case-lambda "Internal invariant violated")])))
    (⟦k⟧ (list {set (-Case-Clo clos)}) H φ Σ))

  (def (scv:make-case-> ℓ Vs H φ Σ ⟦k⟧)
    #:init ()
    #:rest [Vs (listof any/c)]
    (define cases
      (for/list : (Listof -=>) ([V^ (in-list Vs)])
        (match V^
          [(singleton-set (? -=>? C)) C]
          [_ (error 'scv:make-case-> "Internal invariant violated")])))
    (⟦k⟧ (list {set (-Case-> cases)}) H φ Σ)))
