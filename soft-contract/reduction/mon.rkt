#lang typed/racket/base

(provide mon)

(require racket/match
         racket/set
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/definition.rkt"
         "../proof-relation/main.rkt")

(: mon : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define ((mon l³ W-C W-V) M σ ℬ)
  (define Γ (-ℬ-cnd ℬ))
  (match-define (-W C _) W-C)
  (match-define (-W V v) W-V)

  (case (MσΓ⊢V∈C M σ Γ W-C W-V)
    [(✓)
     (values ⊥σ {set (-ΓW Γ (-W (list V) v))} ∅ ∅)]
    [(✗)
     (match-define (Mon-Info l+ _ lo) l³)
     (values ⊥σ ∅ {set (-ΓW Γ (-blm l+ lo (list C) (list V)))} ∅)]
    [(?)
     (error "TODO")]))
