#lang typed/racket/base

(provide reflection@)

(require racket/match
         racket/set
         typed/racket/unit
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt")

(define-unit reflection@
  (import)
  (export reflection^)

  (: V-arity (case-> [(U Clo Case-Clo) → Arity]
                     [V → (Option Arity)]))
  (define V-arity
    (match-lambda
      [_ ???]))
  )
