#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         "../utils/pretty.rkt"
         "../ast/definition.rkt"
         "definition.rkt")

(: blm-arity : ℓ -l Arity (Listof -V) → -blm)
(define blm-arity
  (let ([arity->msg : (Arity → Symbol)
         (match-lambda
           [(? integer? n)
            (format-symbol (case n
                             [(0 1) "~a value"]
                             [else "~a values"])
                           n)]
           [(arity-at-least n)
            (format-symbol "~a+ values" n)])])
    (λ (ℓ lo arity Vs)
      (-blm (ℓ-src ℓ) lo (list (arity->msg arity)) Vs ℓ))))
