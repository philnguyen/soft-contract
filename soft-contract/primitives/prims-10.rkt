#lang typed/racket/base

(provide prims-10@)

(require racket/match
         racket/set
         typed/racket/unit
         "../utils/list.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt")

(define-unit prims-10@
  (import proof-system^ widening^ prim-runtime^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-prim/custom (values ⟪ℋ⟫ ℒ Σ Γ Ws)
    (define-values (Vs ss) (unzip-by -W¹-V -W¹-t Ws))
    {set (-ΓA (-Γ-facts Γ) (-W Vs (apply ?t@ 'values ss)))})
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.2 Exception
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-ext (raise $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦k⟧ (-blm 'Λ 'raise '(raise) (map -W¹-V Ws) (-ℒ-app ℒ)) $ Γ ⟪ℋ⟫ Σ))

  (def-ext (error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦k⟧ (-blm 'Λ 'error '(error) (map -W¹-V Ws) (-ℒ-app ℒ)) $ Γ ⟪ℋ⟫ Σ))

  (def-ext (raise-user-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define blm (-blm 'raise-user-error #|TODO|#
                      'raise-user-error
                      '()
                      (map -W¹-V Ws)
                      (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (def-ext (raise-argument-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₙ symbol?]
              [Wₑ string?]
              [Wᵥ any/c])
    (define blm (-blm 'raise-argument-error #|TODO|#
                      'raise-argument-error
                      (list (-W¹-V Wₙ) (-W¹-V Wₑ))
                      (list (-W¹-V Wᵥ))
                      (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (def-ext (raise-arguments-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (list* Wₙ Wₘ Wᵣ) Ws)
    (define blm (-blm 'raise-arguments-error #|TODO|#
                      'raise-arguments-error
                      (list (-W¹-V Wₙ) (-W¹-V Wₘ))
                      (map -W¹-V Wᵣ)
                      (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  (def-ext (raise-result-error $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₙ symbol?]
              [Wₑ string?]
              [Wᵥ any/c])
    (define blm (-blm 'raise-result-error #|TODO|#
                      'raise-result-error
                      (list (-W¹-V Wₙ) (-W¹-V Wₑ))
                      (list (-W¹-V Wᵥ))
                      (-ℒ-app ℒ)))
    (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.4 Continuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (def-prim/todo call-with-current-continuation ((any/c . -> . any/c) . -> . any/c)) ; FIXME


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

  )
