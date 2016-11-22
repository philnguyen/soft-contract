#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/set
         racket/splicing
         syntax/parse/define
         "../../utils/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")


(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))

(splicing-let-syntax ([compute-frame-roots
                       (syntax-parser
                         [(_) #'∅eq]
                         [(_ root:id) #'(->⟪α⟫s root)]
                         [(_ root:id ...) #'(∪ (->⟪α⟫s root) ...)])])
  (define-simple-macro (with-error-handling (⟦k⟧:id A:id $:id Γ:id ⟪ℋ⟫:id Σ:id)
                         #:roots (root:id ...)
                         e ...)
    (let ([αₖ (⟦k⟧->αₖ ⟦k⟧)]
          [frame-roots (compute-frame-roots root ...)]
          [tail-roots (⟦k⟧->roots ⟦k⟧)])
      (define ⟦k⟧₀ (rt αₖ))
      (define ⟦k⟧* : -⟦k⟧!
        (λ (A $ Γ ⟪ℋ⟫ Σ)
          (cond [(-blm? A)
                 (case (-blm-violator A)
                   [(havoc Λ †) ∅]
                   [else (⟦k⟧₀ A $ Γ ⟪ℋ⟫ Σ)])]
                [else e ...])))
      (set-⟦k⟧->αₖ! ⟦k⟧* αₖ)
      (add-⟦k⟧-roots! ⟦k⟧* (∪ frame-roots tail-roots))
      ⟦k⟧*)))


(splicing-local
    ((define print-cache : (HashTable -blm Void) (make-hash))
     (define print-blames-on-the-fly? #t)
     )

  ;; Base continuation that returns locally finished configuration
  (define/memo (rt [αₖ : -αₖ]) : -⟦k⟧!
    (let ()
      (define ⟦k⟧ : -⟦k⟧!
        (λ (A $ Γ ⟪ℋ⟫ Σ)
          (match A
            [(-blm l+ _ _ _)
             #:when (∋ {seteq 'havoc '† 'Λ} l+)
             ∅]
            [_
             (match-define (-Σ _ _ M) Σ)
             (M⊔! M αₖ Γ A)
             (when (and print-blames-on-the-fly?
                        (-blm? A)
                        (= 0 (set-count (σₖ@ (-Σ-σₖ Σ) αₖ))))
               (hash-ref! print-cache
                          A
                          (λ ()
                            (printf "~a~n" (show-blm A)))))
             {set (-ς↓ αₖ Γ A)}])))
      (set-⟦k⟧->αₖ! ⟦k⟧ αₖ)
      (add-⟦k⟧-roots! ⟦k⟧ ∅eq)
      ⟦k⟧)))
