#lang typed/racket/base

(require racket/match
         racket/set
         racket/contract
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../reduction/compile/app.rkt"
         "def-ext.rkt")

(def-ext (exit l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  ;; HACK
  (define blm (-blm 'Λ 'exit '() '() (-ℒ-app ℒ)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))
