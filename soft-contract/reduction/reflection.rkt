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
         "../signatures.rkt"
         "signatures.rkt")

(define-unit reflection@
  (import static-info^
          val^
          prims^)
  (export reflection^)

  (: V-arity (case-> [(U Clo Case-Clo) → Arity]
                     [V → (Option Arity)]))
  (define V-arity
    (match-lambda
      [(Clo xs _ _) (shape xs)]
      [(Case-Clo cases) (normalize-arity (map V-arity cases))]
      [(Fn:● arity _) arity]
      [(or (And/C #t _ _) (Or/C #t _ _) (? Not/C?) (St/C #t _ _) (? One-Of/C?)) 1]
      [(X/G (? Fn/C? G) _ _) (guard-arity G)]
      [(? -st-p?) 1]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (prim-arity o)]
      [V
       #:when (not (or (Clo? V) (Case-Clo? V))) ; to convince TR
       (log-warning "Warning: call `V-arity` on an obviously non-procedure ~a" V)
       #f]))
  )
