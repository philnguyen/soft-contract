#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/bool
         racket/set
         racket/list
         racket/splicing
         bnf
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit sto@
  (import val^ evl^)
  (export sto^)

  (define ⊥Σᵥ : Σᵥ (hasheq))
  (define ⊥Σₖ : Σₖ (hash))
  (define ⊥Σₐ : Σₐ (hash))
  (define (⊥Σ) (Σ ⊥Σᵥ ⊥Σₖ ⊥Σₐ))

  (: Σᵥ@ : (U Σ Σᵥ) α → V^)
  (splicing-local
      ((define ⟪null?⟫ (αℓ (mk-α (-α:imm 'null?)) +ℓ₀))
       (define cache-listof : (Mutable-HashTable α V^) (make-hasheq)))
    (define (Σᵥ@ Σ α)
      (match (inspect-α α)
        [(-α:imm V) {set V}]
        [(-α:imm:listof x Cₑ ℓ)
         (hash-ref!
          cache-listof α
          (λ ()
            (define flat? (C-flat? Cₑ))
            (define Cₚ (St/C flat? -𝒾-cons
                             (list (αℓ (mk-α (-α:imm Cₑ)) (ℓ-with-id ℓ 'elem))
                                   (αℓ (mk-α (-α:imm:ref-listof x Cₑ ℓ)) (ℓ-with-id ℓ 'rec)))))
            {set (Or/C flat? ⟪null?⟫ (αℓ (mk-α (-α:imm Cₚ)) (ℓ-with-id ℓ 'pair)))}))]
        [(-α:imm:ref-listof x Cₑ ℓ)
         (hash-ref! cache-listof α (λ () {set (X/C (mk-α (-α:imm:listof x Cₑ ℓ)))}))]
        [_ (hash-ref (->Σᵥ Σ) α mk-∅)])))

  (: Σᵥ@* : (U Σ Σᵥ) (Listof α) → (Listof V^))
  (define (Σᵥ@* Σ αs)
    (for/list ([α (in-list αs)]) (Σᵥ@ Σ α)))

  (: Σₖ@ : (U Σ Σₖ) αₖ → Ξ:co^)
  (define (Σₖ@ Σ αₖ) (hash-ref (->Σₖ Σ) αₖ mk-∅))

  (: Σₐ@ : (U Σ Σₐ) Ξ:co → R^)
  (define (Σₐ@ Σ Ξ:co) (hash-ref (->Σₐ Σ) Ξ:co mk-∅))

  (: defined-at? : (U Σ Σᵥ) α → Boolean)
  (define (defined-at? Σ α)
    (match (hash-ref (->Σᵥ Σ) α #f)
      [(? values V^) (not (∋ V^ -undefined))]
      [_ #f]))

  (: construct-call-graph : (U Σ Σₖ) → CG)
  (define (construct-call-graph Σₖ)
    (for*/fold ([CG : CG (hash)])
               ([(α Ξₛs) (in-hash (->Σₖ Σₖ))] [Ξₛ (in-set Ξₛs)])
      (match-define (Ξ:co (K _ αₛ) _ _) Ξₛ)
      (hash-update CG αₛ (λ ([αₜs : (℘ αₖ)]) (set-add αₜs α)) mk-∅))) 

  (: Σᵥ@/ctx : Σ Ctx αℓ → (Values V^ Ctx))
  (define Σᵥ@/ctx
    (match-lambda**
     [(Σ ctx (αℓ α ℓ)) (values (Σᵥ@ Σ α) (Ctx-with-ℓ ctx ℓ))])) 

  #|
  (: unalloc : -σ -δσ -V → (℘ (Listof -V^)))
  ;; Convert a list in the object language into list(s) in the meta language
  (define (unalloc σ δσ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define Tail {set '()})

    (let go : (℘ (Listof -V^)) ([Vₗ : -V V])
      (match Vₗ
        [(-Cons αₕ αₜ)
         (cond
           [(seen-has? αₜ)
            ;; FIXME this list is incomplete and can result in unsound analysis
            ;; if the consumer is effectful
            ;; Need to come up with a nice way to represent an infinite family of lists
            Tail]
           [else
            (seen-add! αₜ)
            (define tails
              (for/union : (℘ (Listof -V^)) ([Vₜ (in-set (σ@ σ δσ αₜ))])
                 (go Vₜ)))
            (define head (σ@ σ δσ αₕ))
            (for/set: : (℘ (Listof -V^)) ([tail (in-set tails)])
                (cons head tail))])]
        [(-b (list)) Tail]
        [_ ∅])))

  (: unalloc-prefix : -σ -δσ -V Natural → (℘ (Pairof (Listof -V^) -V)))
  ;; Extract `n` elements in a list `V` in the object language
  ;; Return the list of values and residual "rest" value
  (define (unalloc-prefix σ δσ V n)
    (let go ([V : -V V] [n : Natural n])
      (cond
        [(<= n 0) {set (cons '() V)}]
        [else
         (match V
           [(-Cons αₕ αₜ)
            (define Vₕs (σ@ σ δσ αₕ))
            (define pairs
              (for/union : (℘ (Pairof (Listof -V^) -V)) ([Vₜ (in-set (σ@ σ δσ αₜ))])
                (go Vₜ (- n 1))))
            (for*/set: : (℘ (Pairof (Listof -V^) -V)) ([pair (in-set pairs)])
              (match-define (cons Vₜs Vᵣ) pair)
              (cons (cons Vₕs Vₜs) Vᵣ))]
           [(-● ps) #:when (∋ ps 'list?) {set (cons (make-list n {set (-● ∅)}) (-● {set 'list?}))}]
           [_ ∅])])))
  |# 

  (: ->Σ (∀ (X) (Σ → X) → (U Σ X) → X))
  (define ((->Σ f) m) (if (Σ? m) (f m) m))
  (define ->Σᵥ (->Σ Σ-val))
  (define ->Σₖ (->Σ Σ-kon))
  (define ->Σₐ (->Σ Σ-evl)) 
  )
