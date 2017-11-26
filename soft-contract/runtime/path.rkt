#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/list
         racket/match
         racket/bool
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit path@
  (import pretty-print^)
  (export path^)

  (define φ₀ : -φ (-φ (hash) (hasheq)))

  (: φ-with-condition : -φ -Γ → -φ)
  (define (φ-with-condition φ Γ)
    (match-define (-φ _ δσ) φ)
    (-φ Γ δσ)) 

  (: t-names : -t → (℘ Integer))
  (define t-names
    (match-lambda
      [(? integer? i) {seteq i}]
      [(? -b?) ∅eq]
      [(-t.@ _ ts) (apply ∪ ∅eq (map t-names ts))]))
  )
