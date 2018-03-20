#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-signature local-prover-core^
  ([partition-sats : (Σ Φ^ V W → (Values Φ^ Φ^ Φ^))]))

(define-signature ext-prover-core^
  ([partition-sats : (Σ Φ^ V W → (Values Φ^ Φ^ Φ^))]))
