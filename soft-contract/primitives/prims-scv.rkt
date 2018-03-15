#lang typed/racket/base

(provide prims-scv@)

(require racket/match
         racket/contract
         typed/racket/unit
         racket/set
         unreachable
         set-extras
         "../utils/debug.rkt"
         "../utils/list.rkt"
         "../utils/patterns.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-scv@
  (import prim-runtime^ evl^
          mon^ step^)
  (export)

  (def (scv:make-case-lambda W ℓ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof any/c)]
    (define clos
      (for/list : (Listof Clo) ([V^ (in-list W)])
        (match V^
          [(singleton-set (? Clo? V)) V]
          [_ (error 'scv:make-case-lambda "Internal invariant violated")])))
    {set (ret! (V->R (Case-Clo clos) Φ^) Ξ Σ)})

  (def (scv:make-case-> W ℓ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof any/c)]
    (define cases
      (for/list : (Listof ==>) ([V^ (in-list W)])
        (match V^
          [(singleton-set (? ==>? C)) C]
          [_ (error 'scv:make-case-> "Internal invariant violated")])))
    {set (ret! (V->R (Case-=> cases) Φ^) Ξ Σ)})

  (def (scv:mon W ℓ Φ^ Ξ Σ)
    #:init ([src symbol?] [C contract?] [V any/c])
    (match-define {singleton-set (-b (and (? symbol?) (app symbol->string l)))} src)
    (mon C V (Ctx l (format "user-of-~a" l) l ℓ) Φ^ Ξ Σ))
  )
