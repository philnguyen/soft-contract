#lang typed/racket/base
(require
 racket/match
 "../utils/non-det.rkt" "../utils/map.rkt"
 "../ast/definition.rkt"
 "../runtime/val.rkt" "../runtime/env.rkt" "../runtime/addr.rkt"
 "../machine/definition.rkt"
 "step-e.rkt" "step-k.rkt" "step-app.rkt" "step-mon.rkt")

(provide ↦ ↦/ς)

(: ↦ : -ς → -Δς*)
;; Steps a full state in the CEΓKSΞ machine
(define ↦
  (match-lambda
    [(-ς (-↓ e ρ) Γ κ σ Ξ M)
     (↦e e ρ Γ κ σ Ξ M)]
    [(-ς (-Mon C V l³ pos) Γ κ σ Ξ M)
     (↦mon C V Γ κ σ Ξ M l³ pos)]
    [(-ς (-App W_f W_xs loc) Γ κ σ Ξ M)
     (↦@ W_f W_xs Γ κ σ Ξ M loc)]
    [(-ς (-define-values l xs e) Γ κ σ Ξ M)
     (↦e e -ρ⊥ Γ (-kont (-φ.def l xs) κ) σ Ξ M)]
    [(-ς (-provide l itms) Γ κ σ Ξ M)
     (match itms
       ['() (↦κ -Void/W Γ κ σ Ξ M)]
       [(cons (-p/c-item x c) itms*)
        (↦e c -ρ⊥ Γ (-kont (-φ.ctc l itms* x) κ) σ Ξ M)])]
    [(-ς (? -W? W) Γ κ σ Ξ M)
     (↦κ W Γ κ σ Ξ M)]
    [(-ς (? -blm? blm) Γ κ σ Ξ M)
     (match κ
       [(? -τ? τ)
        (match/nd: (-kont → -Δς) (hash-ref Ξ τ)
          [κ* (↦blm blm Γ κ* σ Ξ M)])]
       [_ (↦blm blm Γ κ σ Ξ M)])]
    [ς (error '↦ "unexpected: ~a" ς)]))

(: ↦/ς : -ς → -ς*)
;; Like `↦`, but apply all the δs, for compatibility.
;; This is probably bad for performance.
(define (↦/ς ς)
  (match-define (-ς _ _ _ σ Ξ M) ς)
  (match/nd: (-Δς → -ς) (↦ ς)
    [(-Δς E Γ κ δσ δΞ δM)
     (define-values (σ* σ?) (Δ+ δσ σ))
     (define-values (Ξ* Ξ?) (Δ+ δΞ Ξ))
     (define-values (M* M?) (Δ+ δM M))
     (-ς E Γ κ σ* Ξ* M*)]))
