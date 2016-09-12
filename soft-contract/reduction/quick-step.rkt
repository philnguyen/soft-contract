#lang typed/racket/base

(provide run-file havoc-file run-e)

(require "../utils/main.rkt"
         "../ast/main.rkt"
         "../parse/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "compile/kontinuation.rkt"
         "compile/main.rkt"
         "init.rkt"
         racket/set
         racket/match)

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p)
  (define m (file->module p))
  (define-values (σ₁ _) (𝑰 (list m)))
  (run (↓ₘ m) σ₁))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p)
  (define m (file->module p))
  (define-values (σ₁ e₁) (𝑰 (list m)))
  (run (↓ₚ (list m) e₁) σ₁))

(: run-e : -e → (Values (℘ -ΓA) -Σ))
(define (run-e e)
  (define-values (σ₀ _) (𝑰 '()))
  (run (↓ₑ 'top e) σ₀))

(: run : -⟦e⟧! -σ → (Values (℘ -ΓA) -Σ))
(define (run ⟦e⟧! σ)
  (define Σ (-Σ σ (⊥σₖ) (⊥M)))
  (define seen : (HashTable -ς (List Fixnum Fixnum Fixnum)) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ ⟦e⟧! ⊥ρ))

  (define iter : Natural 0)

  (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀ ⊤Γ 𝒞∅)}])
    (unless (set-empty? front)

      (begin
        (define-values (ς↑s ς↓s) (set-partition -ς↑? front))
        (define num-ς↑s (set-count ς↑s))
        (define num-ς↓s (set-count ς↓s))
        (define num-front (set-count front))

        (printf "iter ~a: ~a (~a + ~a) ~n" iter num-front num-ς↑s num-ς↓s)

        #;(begin ; verbose
          (printf " *~n")
          (for ([ς ς↑s])
            (printf "  - ~a~n" (show-ς ς)))
          (printf " *~n")
          (for ([ς ς↓s])
            (printf "  - ~a~n" (show-ς ς))))
        
        (printf "~n")
        (set! iter (+ 1 iter)))

      (define v-Σ
        (let-values ([(v-σ v-σₖ v-M) (-Σ-version Σ)])
          (list v-σ v-σₖ v-M)))
      (define next
        (for/union : (℘ -ς) ([ς front] #:unless (equal? v-Σ (hash-ref seen ς (λ () #f))))
          (hash-set! seen ς v-Σ)
          (↝! ς Σ)))
      (loop! next)))

  (match-let ([(-Σ σ σₖ M) Σ])
    (values (M@ M αₖ₀) Σ)))

(: ↝! : -ς -Σ → (℘ -ς))
;; Perform one "quick-step" on configuration,
;; Producing set of next configurations and store-deltas
(define (↝! ς Σ)
  (match ς
    [(-ς↑ αₖ Γ 𝒞) (↝↑! αₖ Γ 𝒞 Σ)]
    [(-ς↓ αₖ Γ A) (↝↓! αₖ Γ A Σ)]))

(: ↝↑! : -αₖ -Γ -𝒞 -Σ → (℘ -ς))
;; Quick-step on "push" state
(define (↝↑! αₖ Γ 𝒞 Σ)
  (define ⟦k⟧ (rt αₖ))
  (match αₖ
    [(-ℬ ⟦e⟧! ρ)
     (⟦e⟧! ρ Γ 𝒞 Σ ⟦k⟧)]
    [(-ℳ l³ ℓ W-C W-V)
     (mon l³ ℓ W-C W-V Γ 𝒞 Σ ⟦k⟧)]
    [(-ℱ l ℓ W-C W-V)
     (flat-chk l ℓ W-C W-V Γ 𝒞 Σ ⟦k⟧)]
    [_
     (error '↝↑ "~a" αₖ)]))

(: ↝↓! : -αₖ -Γ -A -Σ → (℘ -ς))
;; Quick-step on "pop" state
(define (↝↓! αₖ Γₑₑ A Σ)
  (match-define (-Σ _ σₖ M) Σ)
  (for/union : (℘ -ς) ([κ (σₖ@ σₖ αₖ)])
    (match-define (-κ ⟦k⟧ Γₑᵣ 𝒞ₑᵣ bnd) κ)
    (match-define (-binding f xs x->e) bnd)
    (define fargs (binding->fargs bnd))
    (match A
      [(-W Vs sₐ)
       (define γ (-γ αₖ bnd #f))
       (define Γₑᵣ* (-Γ-plus-γ Γₑᵣ γ))
       (cond
         [(plausible-pc? M Γₑᵣ*)
          (define sₐ*
            (and sₐ
                 (match fargs ; HACK
                   [(-@ 'fc (list x) _)
                    (match Vs
                      [(list (-b #f)) -ff]
                      [(list (-b #t) _) (-?@ 'values -tt x)])]
                   [_ fargs])))
          (⟦k⟧ (-W Vs sₐ*) Γₑᵣ* 𝒞ₑᵣ Σ)]
         [else ∅])]
      [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
       (match-define (-blm l+ lo _ _) blm)
       (case l+
         [(havoc † Λ) ∅]
         [else
          (define γ (-γ αₖ bnd (cons l+ lo)))
          (define Γₑᵣ* (-Γ-plus-γ Γₑᵣ γ))
          (cond
            [(plausible-pc? M Γₑᵣ*)
             (⟦k⟧ blm Γₑᵣ* 𝒞ₑᵣ Σ)]
            [else ∅])])])))
