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
  (define blm (-blm 'Λ 'exit '() '()))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

(def-ext (error l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  ;; HACK
  (define blm (-blm l 'error '(error) (map -W¹-V Ws)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))
