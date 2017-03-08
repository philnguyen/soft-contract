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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.5 Continuation Marks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (continuation-mark-set-first $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (⟦k⟧ (-W -●.Vs #f) $ Γ ⟪ℋ⟫ Σ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.7 Exiting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (exit $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  ;; HACK
  (define blm (-blm 'Λ 'exit '() '() (-ℒ-app ℒ)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

(def-ext (raise-argument-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wₙ symbol?]
            [Wₑ string?]
            [Wᵥ any/c])
  (define blm (-blm (ℓ-src (-ℒ-app ℒ))
                    'raise-argument-error
                    (list (-W¹-V Wₙ) (-W¹-V Wₑ))
                    (list (-W¹-V Wᵥ))
                    (-ℒ-app ℒ)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

(def-ext (raise-arguments-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (list* Wₙ Wₘ Wᵣ) Ws)
  (define blm (-blm (ℓ-src (-ℒ-app ℒ))
                    'raise-arguments-error
                    (list (-W¹-V Wₙ) (-W¹-V Wₘ))
                    (map -W¹-V Wᵣ)
                    (-ℒ-app ℒ)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

(def-ext (raise-result-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  #:domain ([Wₙ symbol?]
            [Wₑ string?]
            [Wᵥ any/c])
  (define blm (-blm (ℓ-src (-ℒ-app ℒ))
                    'raise-argument-error
                    (list (-W¹-V Wₙ) (-W¹-V Wₑ))
                    (list (-W¹-V Wᵥ))
                    (-ℒ-app ℒ)))
  (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))
