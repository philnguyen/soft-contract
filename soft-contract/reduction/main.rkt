#lang typed/racket/base
(require
 racket/match
 "../utils.rkt" "../runtime.rkt" "../machine.rkt"
 "step-e.rkt" "step-k.rkt" "step-app.rkt" "step-mon.rkt")

(provide ↦)

(: ↦ : -ς → -Δς*)
;; Steps a full state in the CEΓKSΞ machine
(define ↦
  (match-lambda
    [(-ς (-↓ e ρ) Γ κ σ Ξ M)
     (↦e e ρ Γ κ σ Ξ M)]
    [(-ς (-Mon C V l³ pos) Γ κ σ Ξ M)
     (↦mon C V Γ κ σ Ξ M l³ pos)]
    [(-ς (-FC C V l) Γ κ σ Ξ M)
     (↦FC C V Γ κ σ Ξ M l)]
    [(-ς (? -W? W) Γ κ σ Ξ M)
     (↦κ W Γ κ σ Ξ M)]
    [(-ς (? -blm? blm) Γ κ σ Ξ M)
     (match κ
       [(? -τ? τ)
        (match/nd: (-kont → -Δς) (hash-ref Ξ τ)
          [κ* (↦blm blm Γ κ* σ Ξ M)])]
       [_ (↦blm blm Γ κ σ Ξ M)])]
    [ς (error '↦ "unexpected: ~a" ς)]))
