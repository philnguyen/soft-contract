#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/set
         racket/splicing
         syntax/parse/define
         "../../utils/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(define-simple-macro (with-error-handling (⟦k⟧:id A:id $:id Γ:id 𝒞:id Σ:id) e ...)
  (let ([αₖ (⟦k⟧->αₖ ⟦k⟧)])
    (define ⟦k⟧* : -⟦k⟧!
      (λ (A $ Γ 𝒞 Σ)
        (cond [(-blm? A)
               (case (-blm-violator A)
                 [(havoc Λ †) ∅]
                 [else {set (-ς↓ αₖ Γ A)}])]
              [else e ...])))
    (set-⟦k⟧->αₖ! ⟦k⟧* αₖ)
    ⟦k⟧*))

(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))

;; TMP hack for part of root set from stack frames
(splicing-let ([m ((inst make-hasheq -⟦k⟧! (℘ -α)))])
  
  (define (add-⟦k⟧-roots [⟦k⟧ : -⟦k⟧!] [αs : (℘ -α)]) : Void
    (hash-update! m ⟦k⟧ (λ ([αs₀ : (℘ -α)]) (∪ αs₀ αs)) →∅))
  
  ;; Return the root set spanned by the stack chunk for current block
  (define (⟦k⟧->roots [⟦k⟧ : -⟦k⟧!])
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αs "nothing for ~a" ⟦k⟧)))))

;; TMP hack for mapping stack to stack address to return to
(splicing-let ([m ((inst make-hasheq -⟦k⟧! -αₖ))])

  (define (set-⟦k⟧->αₖ! [⟦k⟧ : -⟦k⟧!] [αₖ : -αₖ]) : Void
    (hash-update! m ⟦k⟧
                  (λ ([αₖ₀ : -αₖ]) ; just for debugging
                    (assert (equal? αₖ₀ αₖ))
                    αₖ₀)
                  (λ () αₖ)))
  
  (define (⟦k⟧->αₖ [⟦k⟧ : -⟦k⟧!]) : -αₖ
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αₖ "nothing for ~a" ⟦k⟧)))))
