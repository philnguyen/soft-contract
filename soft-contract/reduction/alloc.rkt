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
         bnf
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         )

(define-unit alloc@
  (import static-info^ sto^)
  (export alloc^)

  (: mutable? : α → Boolean)
  (define (mutable? α)
    (match (inspect-α α)
      [(-α:x x _) (assignable? x)]
      [(-α:fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α:idx?) #t]
      [_ #f]))

  (: bind-args! : Ρ -formals W ℓ Φ^ H Σ → Ρ)
  (define (bind-args! Ρ₀ xs W ℓ Φ^ H Σ)
    ???) 

  (: H+ : H ℓ (U ⟦E⟧ V) (U 'app 'mon) → H)
  (define (H+ H src tgt type) ???)

  (define H₀ (mk-H (-H:edges '())))

  )

(define-substructs -H
  [-H:edges (Listof Edge)])

(Edge . ::= . (Edge [src : ℓ] [tgt : (U ⟦E⟧ V)]))
