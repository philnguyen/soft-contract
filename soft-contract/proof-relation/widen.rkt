#lang typed/racket/base

(provide widening@)

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/list
         racket/set
         racket/bool
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit widening@
  (import)
  (export widening^)

  (: V⊕ : -V^ -V^ → -V^)
  (define (V⊕ V₁ V₂)
    (error 'TODO))

  )

