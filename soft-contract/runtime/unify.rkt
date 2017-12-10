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

  (: unify-V^ : Uni -V^ -V^ → (Option Uni))
  (define (unify-V^ m V^₁ V^₂)
    (for/or : (Option Uni) ([V₁ (in-set V^₁)])
      (for/or : (Option Uni) ([V₂ (in-set V^₂)])
        (match* (V₁ V₂)
          [((? -t? t₁) (? -t? t₂)) (Bij-ext m t₁ t₂)]
          [(_ _) (and (equal? V₁ V₂) m)]))))

  (: unify-V^s : Uni (Listof -V^) (Listof -V^) → (Option Uni))
  (define (unify-V^s m Vs₁ Vs₂)
    (match* (Vs₁ Vs₂)
      [('() '()) m]
      [((cons V₁ Vs₁*) (cons V₂ Vs₂*))
       (match (unify-V^ m V₁ V₂)
         [(? values m*) (unify-V^s m* Vs₁* Vs₂*)]
         [#f #f])]
      [(_ _) #f]))

  (: unify-Bl : -Block -Block → (Option Uni))
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

  (: φ⊑/m? : Uni -φ -φ → Boolean)
  (define (φ⊑/m? m φ₁ φ₂)
    (and
     #;(same-δσ? m (-φ-cache φ₁) (-φ-cache φ₂))
     (let go ([maps : (Listof (Pairof -t -t)) (hash->list (Bij-fw m))]
              [Γ₁ : -Γ (-φ-condition φ₁)]
              [Γ₂ : -Γ (-φ-condition φ₂)])
       (match maps
         [(cons (cons s₁ s₂) maps*)
          (and (equal? (hash-ref Γ₁ (list s₁) #f) (hash-ref Γ₂ (list s₂) #f))
               (go maps* (hash-remove Γ₁ (list s₁)) (hash-remove Γ₂ (list s₂))))]
         ['()
          (for/and : Boolean ([(ts ps) (in-hash Γ₂)])
            (equal? ps (hash-ref Γ₁ ts #f)))]))))

  (: rename-V^ : (HashTable -t -t) -V^ → -V^)
  (define (rename-V^ m V^)
    (for/set: : -V^ ([V (in-set V^)])
      (if (-t? V) (hash-ref m V (λ () V)) V)))

  (: Γ+ : -Γ (HashTable -t -t) -Γ → -Γ)
  (define (Γ+ Γₑᵣ m Γₑₑ)
    (for*/fold ([Γ* : -Γ Γₑᵣ])
               ([(tₑₑ tₑᵣ) (in-hash m)]
                [ps (in-value (hash-ref Γₑₑ (list tₑₑ) #f))]
                #:when ps)
      (hash-update Γ* (list tₑᵣ) (λ ([ps₀ : (℘ -h)]) (∪ ps₀ ps)) mk-∅)))
  )
