#lang typed/racket/base

(provide alloc@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function const)
         racket/set
         racket/list
         racket/match
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit alloc@
  (import)
  (export alloc^)

  (: mutable? : α → Boolean)
  (define (mutable? α)
    (match (inspect-α α)
      [(-α.x x _) (assignable? x)]
      [(-α.fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α.idx?) #t]
      [_ #f])))

