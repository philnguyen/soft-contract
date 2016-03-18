#lang typed/racket/base

(provide (all-defined-out))

(require "definition.rkt")

(: ρ++ : -ρ -Δρ → -ρ)
(define (ρ++ ρ δρ)
  (for/fold ([ρ : -ρ ρ]) ([(x α) δρ])
    (hash-set ρ x α)))
