#lang typed/racket/base

(provide run-file havoc-file run-e run)

(require
 racket/match racket/set
 "../utils/main.rkt"
 "../ast/main.rkt"
 "../parse/main.rkt"
 "../runtime/main.rkt"
 (only-in "../proof-relation/main.rkt" es⊢ₑₓₜe)
 (only-in "../proof-relation/ext/z3.rkt" z3⊢)
 "step.rkt"
 "init.rkt")

(: run-file : Path-String → (Values (℘ -A) #|debugging|# -M -Ξ))
(define (run-file p)
  (define m (file->module p))
  (define-values (σ₁ _) (𝑰 (list m)))
  (define-values (As M Ξ σ) (run (⇓ₘ m) σ₁))
  (values As M Ξ))

(: havoc-file : Path-String → (Values (℘ -A) #|debugging|# -M -Ξ))
(define (havoc-file p)
  (define m (file->module p))
  (define-values (σ₁ e₁) (𝑰 (list m)))
  (define-values (As M Ξ σ) (run (⇓ₚ (list m) e₁) σ₁))
  #;(begin
    (printf "final σ:~n")
    (for ([r (show-σ σ)])
      (printf "  - ~a~n" r)))
  (values As M Ξ))

(: run-e : -e → (Values (℘ -A) #|for debugging|# -M -Ξ))
(define (run-e e)
  (define-values (σ₀ _) (𝑰 '()))
  (define-values (As M Ξ σ) (run (⇓ 'top e) σ₀))
  (values As M Ξ))

(: run : -⟦e⟧ -σ → (Values (℘ -A) #|for debugging|# -M -Ξ -σ))
;; Run compiled program on initial heap
(define (run ⟦e⟧₀ σ₀)
  
  (: loop : (HashTable -τ -σ) (℘ -τ) (℘ -Co) -M -Ξ -σ → (Values -M -Ξ -σ))
  (define (loop seen τs Cos M Ξ σ)
    (cond
      [(and (set-empty? τs) (set-empty? Cos))
       (values M Ξ σ)]
      [else
       
       ;; Widen global tables
       (define-values (δM δΞ δσ) (⊔³ (ev* M Ξ σ τs) (co* M Ξ σ Cos)))
       (define-values (M* Ξ* σ*) (⊔³ (values M Ξ σ) (values δM δΞ δσ)))

       #;(begin
         (printf "δM:~n~a~n" (show-M δM))
         (printf "δΞ:~n~a~n" (show-Ξ δΞ))
         (printf "δσ:~n~a~n" (show-σ δσ))
         (printf "~n"))

       ;; Check for un-explored configuation (≃ ⟨e, ρ, σ⟩)
       (define-values (τs* seen*)
         (for/fold ([τs* : (℘ -τ) ∅] [seen* : (HashTable -τ -σ) seen])
                   ([τ (in-hash-keys δΞ)] #:unless (equal? (hash-ref seen τ #f) σ*))
           (values (set-add τs* τ) (hash-set seen* τ σ*))))
       (define Cos*
         (∪ (for*/set: : (℘ -Co) ([(τ As) (in-hash δM)] #:unless (set-empty? As)
                                  [ℛ (in-set (Ξ@ Ξ* τ))])
              (-Co ℛ τ As))
            (for*/set: : (℘ -Co) ([(τ ℛs) (in-hash δΞ)]
                                  [As (in-value (M@ M* τ))] #:unless (set-empty? As)
                                  [ℛ (in-set ℛs)])
              (-Co ℛ τ As))))
       
       (loop seen* τs* Cos* M* Ξ* σ*)]))

  (define τ₀ (-ℬ ⟦e⟧₀ ℒ∅))
  (define-values (M Ξ σ)
    (parameterize ([es⊢ₑₓₜe z3⊢])
      (loop (hash τ₀ σ₀) {set τ₀} ∅ ⊥M ⊥Ξ σ₀)))
  (values (M@ M τ₀) M Ξ σ))
