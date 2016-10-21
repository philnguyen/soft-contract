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
  (define seen↑ : (HashTable -ς↑ (List (HashTable -α -σr) (HashTable -αₖ (℘ -ΓA)))) (make-hash))
  (define seen↓ : (HashTable -ς↓ (℘ -κ)) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ '() ⟦e⟧! ⊥ρ))

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

          (begin ; interactive
            (define ςs-list
              (append (set->list ς↑s) (set->list ς↓s)))
            (define ς->i
              (for/hash : (HashTable -ς Integer) ([(ς i) (in-indexed ςs-list)])
                (values ς i))))
          
          (printf " *~n")
          (for ([ς ς↑s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))
          (printf " *~n")
          (for ([ς ς↓s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))

          (begin ; interactive
            (printf "~nchoose [0-~a|ok|done]: " (sub1 (hash-count ς->i)))
            (match (read)
              [(? exact-integer? i) (set! front (set (list-ref ςs-list i)))]
              ['done (error "DONE")]
              [_ (void)]))
          )
        
        (printf "~n")
        (set! iter (+ 1 iter)))

      (define next
        (for/union : (℘ -ς) ([ς front])
          (cond
            [(-ς↑? ς)
             (define vs↑ : (List (HashTable -α -σr) (HashTable -αₖ (℘ -ΓA)))
               (list (span-σ (-σ-m (-Σ-σ Σ)) (ς->αs ς))
                     (span-M (VMap-m (-Σ-M Σ)) (ς->αₖs ς))))
             (cond
               [(equal? vs↑ (hash-ref seen↑ ς #f)) ∅]
               [else
                #;(match-let ([(list σ* M*) vs↑])

                  (: δσ : (HashTable -α -σr) (HashTable -α -σr) → (HashTable -α (℘ -V)))
                  (define (δσ σ₁ σ₀)
                    (define m₁ (map/hash -σr-vals σ₁))
                    (define m₀ (map/hash -σr-vals σ₀))
                    (mmap-subtract m₁ m₀))

                  (match-define (list σ₀ M₀)
                    (hash-ref seen↑ ς
                              (λ ()
                                (ann (list ((inst hash -α -σr))
                                           ((inst hash -αₖ (℘ -ΓA))))
                                     (List (HashTable -α -σr)
                                           (HashTable -αₖ (℘ -ΓA)))))))
                  (printf "~a~n  New σ:~a~n  New M: ~a~n~n"
                          (show-ς ς)
                          (show-σ (δσ σ* σ₀))
                          (show-M (mmap-subtract M* M₀))))
                (hash-set! seen↑ ς vs↑)
                (↝! ς Σ)])]
            [else
             (define vs↓
               (match-let ([(-ς↓ αₖ _ _) ς])
                 (σₖ@ (-Σ-σₖ Σ) αₖ)))
             (cond
               [(equal? vs↓ (hash-ref seen↓ ς #f)) ∅]
               [else
                #;(printf "~a~n  Last seen: ~a~n  Now: ~a~n~n"
                          (show-ς ς)
                          (hash-ref seen↓ ς #f)
                          vs↓)
                (hash-set! seen↓ ς vs↓)
                (↝! ς Σ)])])))
      (loop! next)))

  (match-let ([(-Σ σ σₖ M) Σ])
    (values (M@ M αₖ₀) Σ)))

(: ς->αs : -ς↑ → (℘ -α))
(define ς->αs
  (match-lambda
    [(-ς↑ αₖ _ _) (αₖ->αs αₖ)]))

(: αₖ->αs : -αₖ → (℘ -α))
(define αₖ->αs
  (match-lambda
    [(-ℬ _ _ ρ) (ρ->αs ρ)]
    [(-ℳ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (V->αs C) (V->αs V))]
    [(-ℱ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (V->αs C) (V->αs V))]))

(: ς->αₖs : -ς↑ → (℘ -αₖ))
(define ς->αₖs
  (match-lambda
    [(-ς↑ _ Γ _) (Γ->αs Γ)]))

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
    [(-ℬ _ ⟦e⟧! ρ)
     (⟦e⟧! ρ Γ 𝒞 Σ ⟦k⟧)]
    [(-ℳ _ l³ ℓ W-C W-V)
     (mon l³ ℓ W-C W-V Γ 𝒞 Σ ⟦k⟧)]
    [(-ℱ _ l ℓ W-C W-V)
     (flat-chk l ℓ W-C W-V Γ 𝒞 Σ ⟦k⟧)]
    [_
     (error '↝↑ "~a" αₖ)]))

(: ↝↓! : -αₖ -Γ -A -Σ → (℘ -ς))
;; Quick-step on "pop" state
(define (↝↓! αₖ Γₑₑ A Σ)
  (match-define (-Σ _ σₖ M) Σ)
  (for/union : (℘ -ς) ([κ (σₖ@ σₖ αₖ)])
    (match-define (-κ ⟦k⟧ Γₑᵣ 𝒞ₑᵣ sₕ sₓs) κ)
    (define fargs (apply -?@ sₕ sₓs))
    (match A
      [(-W Vs sₐ)
       (define γ (-γ αₖ #f sₕ sₓs))
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
          (define t₀ (current-milliseconds))
          (with-debugging/off
            ((ans) (⟦k⟧ (-W Vs sₐ*) Γₑᵣ* 𝒞ₑᵣ Σ))
            (define δt (- (current-milliseconds) t₀))
            (printf "ς↓: ~a ~a -> ~a ~a: ~ams~n"
                    (show-A A)
                    (show-Γ Γₑₑ)
                    (show-αₖ αₖ)
                    (show-κ κ)
                    δt)
            (for ([ς ans])
              (printf "  - ~a~n" (show-ς ς)))
            (printf "~n"))]
         [else ∅])]
      [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
       (match-define (-blm l+ lo _ _) blm)
       (case l+
         [(havoc † Λ) ∅]
         [else
          (define γ (-γ αₖ (cons l+ lo) sₕ sₓs))
          (define Γₑᵣ* (-Γ-plus-γ Γₑᵣ γ))
          (cond
            [(plausible-pc? M Γₑᵣ*)
             (⟦k⟧ blm Γₑᵣ* 𝒞ₑᵣ Σ)]
            [else ∅])])])))
