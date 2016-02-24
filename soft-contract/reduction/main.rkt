#lang typed/racket/base

(provide run-files run run-e)

(require
 racket/match racket/set
 "../utils/main.rkt"
 "../ast/main.rkt"
 "../parse/main.rkt"
 "../runtime/main.rkt"
 (only-in "../proof-relation/main.rkt" Γ⊢ₑₓₜ)
 (only-in "../proof-relation/ext/z3.rkt" z3⊢)
 "step.rkt" #;"init.rkt")

(: run-files : Path-String * → (℘ -A))
(define (run-files . ps)
  (define ms (files->modules ps))
  (define-values (σ₀ e₀) (values ⊥σ (-b (void))) #;(𝑰 ms))
  (define-values (As G M Ξ σ) (run (⇓ₚ ms e₀) σ₀))
  As)

(: run-e : -e → (Values Sexp #|for debugging|# Sexp Sexp Sexp Sexp))
(define (run-e e)
  (define-values (As G M Ξ σ) (run (⇓ e) ⊥σ))
  (values (set-map As show-A) (show-G G) (show-M M) (show-Ξ Ξ) (show-σ σ)))

(: run : -⟦e⟧ -σ → (Values (℘ -A) #|for debugging|# -G -M -Ξ -σ))
;; Run compiled program on initial heap
(define (run ⟦e⟧₀ σ₀)
  
  (: loop : (HashTable -ℬ -σ) (℘ -ℬ) (℘ -Co) -G -M -Ξ -σ → (Values -G -M -Ξ -σ))
  (define (loop seen ℬs Cos G M Ξ σ)
    (cond
      [(and (set-empty? ℬs) (set-empty? Cos))
       (values G M Ξ σ)]
      [else
       
       ;; Widen global tables
       (define-values (δM δΞ δσ) (⊔³ (ev* G M Ξ σ ℬs) (co* G M Ξ σ Cos)))
       (define-values (M* Ξ* σ*) (⊔³ (values M Ξ σ) (values δM δΞ δσ)))
       (define G* (G⊔ G δM Ξ))

       ;; Check for un-explored configuation (≃ ⟨e, ρ, σ⟩)
       (define-values (ℬs* seen*)
         (for/fold ([ℬs* : (℘ -ℬ) ∅] [seen* : (HashTable -ℬ -σ) seen])
                   ([ℬ (in-hash-keys δΞ)] #:unless (equal? (hash-ref seen -ℬ #f) σ*))
           (values (set-add ℬs* ℬ) (hash-set seen* ℬ σ*))))
       (define Cos*
         (∪ (for*/set: : (℘ -Co) ([(ℬ As) (in-hash δM)] #:unless (set-empty? As)
                                  [ℛ (in-set (Ξ@ Ξ* ℬ))])
              (-Co ℛ As))
            (for*/set: : (℘ -Co) ([(ℬ ℛs) (in-hash δΞ)]
                                  [As (in-value (M@ M* ℬ))] #:unless (set-empty? As)
                                  [ℛ (in-set ℛs)])
              (-Co ℛ As))))
       
       (loop seen* ℬs* Cos* G* M* Ξ* σ*)]))

  (define ℬ₀ (-ℬ ⟦e⟧₀ ⊥ρ))
  (define-values (G M Ξ σ)
    (parameterize ([Γ⊢ₑₓₜ z3⊢])
      (loop (hash ℬ₀ σ₀) {set ℬ₀} ∅ ⊥G ⊥M ⊥Ξ σ₀)))
  (values (M@ M ℬ₀) G M Ξ σ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊔³ x y)
  (let-values ([(x₁ x₂ x₃) x]
               [(y₁ y₂ y₃) y])
    (values (⊔/m x₁ y₁) (⊔/m x₂ y₂) (⊔/m x₃ y₃))))

(: G⊔ : -G -ΔM -Ξ → -G)
(define (G⊔ G δM Ξ)
  (for*/fold ([G : -G G])
             ([(ℬ As) δM]
              [A (in-set As)]
              [Γₐ (in-value (-A-cnd A))]
              [Wₐ (in-value (-A-res A))] #:when (-W? Wₐ)
              [ℛ (Ξ@ Ξ ℬ)])
    (match-define (-W _ sₐ) Wₐ)
    (match-define (-ℛ ℬ₀ ℋ₀) ℛ)
    (match-define (-ℋ Γ₀ 𝒳 s bnds ℰ) ℋ₀)
    (match-define (-ℬ ⟦e⟧₀ ρ₀) ℬ₀)
    (define args (map (inst cdr Symbol -s) bnds))
    (define fargs (apply -?@ s args))
    (cond
      [fargs
       (define k (-G.key (-γ fargs) (m↓ ρ₀ (fv fargs))))
       (define 𝒳
         (for*/hash : -𝒳 ([x-s bnds]
                          [e (in-value (cdr x-s))] #:when e
                          [x (in-value (car x-s))])
           (values x e)))
       (⊔ G k (-G.val Γₐ sₐ 𝒳))]
      [else G])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(module+ test
  (require typed/rackunit)
  )
