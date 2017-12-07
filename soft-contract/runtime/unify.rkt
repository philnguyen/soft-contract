#lang typed/racket/base

(provide unify@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit unify@
  (import sto^)
  (export unify^) 

  (: unify-V^ : Bij -V^ -V^ → (Option Bij))
  (define (unify-V^ m V^₁ V^₂)
    (for/or : (Option Bij) ([V₁ (in-set V^₁)])
      (for/or : (Option Bij) ([V₂ (in-set V^₂)])
        (match* (V₁ V₂)
          [((? integer? s₁) (? integer? s₂)) (Bij-ext m s₁ s₂)]
          [(_ _) (and (equal? V₁ V₂) m)]))))

  (: unify-V^s : Bij (Listof -V^) (Listof -V^) → (Option Bij))
  (define (unify-V^s m Vs₁ Vs₂)
    (match* (Vs₁ Vs₂)
      [('() '()) m]
      [((cons V₁ Vs₁*) (cons V₂ Vs₂*))
       (match (unify-V^ m V₁ V₂)
         [(? values m*) (unify-V^s m* Vs₁* Vs₂*)]
         [#f #f])]
      [(_ _) #f]))

  (: unify-Bl : -Block -Block → (Option Bij))
  (define unify-Bl
    (match-lambda**
     [((-B Vₕ₁ Vₓs₁ ℓ) (-B Vₕ₂ Vₓs₂ ℓ))
      (unify-V^s Bij-empty (cons {set Vₕ₁} Vₓs₁) (cons {set Vₕ₂} Vₓs₂))]
     [((-M ctx C₁ V₁) (-M ctx C₂ V₂))
      (unify-V^s Bij-empty (list C₁ V₁) (list C₂ V₂))]
     [((-F l ℓ C₁ V₁) (-F l ℓ C₂ V₂))
      (unify-V^s Bij-empty (list C₁ V₁) (list C₂ V₂))]
     [((-HV t) (-HV t)) Bij-empty]
     [(_ _) #f]))

  (: φ⊑/m? : Bij -φ -φ → Boolean)
  (define (φ⊑/m? m φ₁ φ₂)
    (and
     #;(same-δσ? m (-φ-cache φ₁) (-φ-cache φ₂))
     (let go ([maps : (Listof (Pairof Integer Integer)) (hash->list (Bij-fw m))]
              [Γ₁ : -Γ (-φ-condition φ₁)]
              [Γ₂ : -Γ (-φ-condition φ₂)])
       (match maps
         [(cons (cons s₁ s₂) maps*)
          (and (equal? (hash-ref Γ₁ (list s₁) #f) (hash-ref Γ₂ (list s₂) #f))
               (go maps* (hash-remove Γ₁ (list s₁)) (hash-remove Γ₂ (list s₂))))]
         ['()
          (for/and : Boolean ([(ts ps) (in-hash Γ₂)])
            (equal? ps (hash-ref Γ₁ ts #f)))]))))

  (: rename-V^ : (HashTable Integer Integer) -V^ → -V^)
  (define (rename-V^ m V^)
    (for/set: : -V^ ([V (in-set V^)])
      (match V
        [(? integer? s) (hash-ref m s (λ () s))]
        [V V])))
  )
