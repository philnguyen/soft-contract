#lang typed/racket/base

(provide unify@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit unify@
  (import sto^ path^ widening^)
  (export unify^)

  (: unify-V : Uni -V -V → (Option Uni))
  (define (unify-V m V₁ V₂)
    (match* (V₁ V₂)
      [((? -t? t₁) (? -t? t₂))
       #:when (not (and (-b? t₁) (-b? t₂)))
       (Bij-ext m t₁ t₂)]
      [(_ _) (and (equal? V₁ V₂) m)]))

  (: unify-V^ : Uni -V^ -V^ → (Option Uni))
  (define (unify-V^ m V^₁ V^₂)
    (cond [(and (set-empty? V^₁) (set-empty? V^₂)) Bij-empty]
          [else (for/or : (Option Uni) ([V₁ (in-set V^₁)])
                  (for/or : (Option Uni) ([V₂ (in-set V^₂)])
                    (unify-V m V₁ V₂)))]))

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
    (match-define (-φ Γ₁ δσ₁) φ₁)
    (match-define (-φ Γ₂ δσ₂) φ₂)
    (and (σ⊑/m? m δσ₁ δσ₂) (Γ⊑/m? m Γ₁ Γ₂)))

  (: Γ⊑/m? : Uni -Γ -Γ → Boolean)
  (define (Γ⊑/m? m Γ₁ Γ₂)
    (let go ([maps : (Listof (Pairof -t -t)) (hash->list (Bij-fw m))]
             [Γ₁ : -Γ Γ₁]
             [Γ₂ : -Γ Γ₂])
      (match maps
        [(cons (cons s₁ s₂) maps*)
         (and (equal? (hash-ref Γ₁ s₁ #f) (hash-ref Γ₂ s₂ #f))
              (go maps* (hash-remove Γ₁ s₁) (hash-remove Γ₂ s₂)))]
        ['()
         (for/and : Boolean ([(ts ps) (in-hash Γ₂)])
           (equal? ps (hash-ref Γ₁ ts #f)))])))

  (: σ⊑/m? : Uni -σ -σ → Boolean)
  (define (σ⊑/m? m σ₁ σ₂)
    (for/and : Boolean ([(α V) (in-hash σ₁)])
      (and (unify-V^ m V (hash-ref σ₂ α mk-∅)) #t)))

  (: σ-compat/m? : Uni -σ -σ → Boolean)
  (define (σ-compat/m? m σ₁ σ₂)
    (: compat-V? : -V -V → Boolean)
    (define (compat-V? V₁ V₂)
      (cond [(and (-t? V₁) (not (-b? V₁)) (-t? V₂) (not (-b? V₂)))
             (and (Bij-ext m V₁ V₂) #t)]
            [(or (-t? V₁) (-t? V₂)) #f]
            [else (and (compat? φ₀ V₁ V₂) #t)]))
    (: compat-V^? : -V^ -V^ → Boolean)
    (define (compat-V^? V₁^ V₂^)
      (for/or : Boolean ([V₁ (in-set V₁^)])
        (for/or : Boolean ([V₂ (in-set V₂^)])
          (compat-V? V₁ V₂))))
    (for/and : Boolean ([(α V^) (in-hash σ₁)])
      (compat-V^? V^ (hash-ref σ₂ α mk-∅))))

  (: rename-V^ : (HashTable -t -t) -V^ → -V^)
  (define (rename-V^ m V^)
    (for/set: : -V^ ([V (in-set V^)])
      (if (-t? V) (hash-ref m V (λ () V)) V)))

  (: Γ+ : -Γ (HashTable -t -t) -Γ → -Γ)
  (define (Γ+ Γₑᵣ m Γₑₑ)
    
    (: translate : (℘ -h) → (℘ -h))
    (define (translate ps)
      (: translate-h : -h → (Option -h))
      (define translate-h
        (match-lambda
          [(-</c t) (cond [(translate-t t) => -</c] [else #f])]
          [(-≤/c t) (cond [(translate-t t) => -≤/c] [else #f])]
          [(->/c t) (cond [(translate-t t) => ->/c] [else #f])]
          [(-≥/c t) (cond [(translate-t t) => -≥/c] [else #f])]
          [h h]))

      (: translate-t : -t → (Option -t))
      (define (translate-t t)
        (if (-b? t) t (hash-ref m t #f)))

      (for*/set: : (℘ -h) ([p (in-set ps)]
                           [p* (in-value (translate-h p))]
                           #:when p*)
        p*))
    
    (for*/fold ([Γ* : -Γ Γₑᵣ])
               ([(tₑₑ tₑᵣ) (in-hash m)]
                [ps (in-value (hash-ref Γₑₑ tₑₑ mk-∅))]
                [ps* (in-value (translate ps))]
                #:unless (set-empty? ps*))
      (hash-update Γ* tₑᵣ (λ ([ps₀ : (℘ -h)]) (∪ ps₀ ps*)) mk-∅)))
  )
