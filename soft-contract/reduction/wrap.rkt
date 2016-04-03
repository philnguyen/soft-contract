#lang typed/racket/base

(provide ↝.wrap.st)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         "helpers.rkt")

(: ↝.wrap.st : -struct-info (Listof -α) -α.st Mon-Info → -⟦ℰ⟧)
(define ((↝.wrap.st s αs α l³) ⟦e⟧)
  (define muts (-struct-info-mutables s))
  (define αs* : (Listof (Option -α))
    (for/list ([(α i) (in-indexed αs)])
      (and (∋ muts i) α)))
  (define V* (-St* s αs* α l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.wrap.st s αs α l³ ℰ))
      (λ (σ* Γ* W)
        (match-define (-W (list V) v) W) ; only used internally, should be safe
        (values (⊔ ⊥σ α V) {set (-ΓW Γ* (-W (list V*) v))} ∅ ∅)))
     (⟦e⟧ M σ ℒ))))
