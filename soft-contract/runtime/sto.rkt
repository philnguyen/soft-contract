#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/bool
         racket/set
         racket/list
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit sto@
  (import pretty-print^ local-prover^ path^ val^ prim-runtime^ static-info^ widening^)
  (export sto^)

  (define ⊥σ : -σ (hasheq))

  (: σ⊔! : -Σ ⟪α⟫ -V^ → Void)
  (define (σ⊔! Σ α V)
    (set--Σ-σ! Σ (hash-update (-Σ-σ Σ) α (λ ([V₀ : -V^]) (V⊕ V₀ V)) mk-∅)))

  (splicing-local
      ((define ⟪null?⟫ (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm 'null?)) +ℓ₀))
       (define cache-listof : (Mutable-HashTable ⟪α⟫ (℘ -V)) (make-hasheq)))
    (: σ@ : (U -Σ -σ) -δσ ⟪α⟫ → -V^)
    (define (σ@ m δσ ⟪α⟫)
      (match (⟪α⟫->-α ⟪α⟫)
        [(-α.imm V) {set V}]
        [(-α.imm-listof x Cₑ ℓ)
         (hash-ref!
          cache-listof ⟪α⟫
          (λ ()
            (define flat? (C-flat? Cₑ))
            (define Cₚ (-St/C flat? -𝒾-cons
                              (list (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm Cₑ)) (ℓ-with-id ℓ 'elem))
                                    (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm-ref-listof x Cₑ ℓ)) (ℓ-with-id ℓ 'rec)))))
            {set (-Or/C flat? ⟪null?⟫ (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm Cₚ)) (ℓ-with-id ℓ 'pair)))}))]
        [(-α.imm-ref-listof x Cₑ ℓ)
         (hash-ref! cache-listof ⟪α⟫ (λ () {set (-x/C (-α->⟪α⟫ (-α.imm-listof x Cₑ ℓ)))}))]
        [α
         (define σ (if (-Σ? m) (-Σ-σ m) m))
         (hash-ref σ ⟪α⟫ (λ () (match α
                                 ; ok for hv addresses to not exist
                                 ; TODO clean up
                                 [(-α.hv _) ∅]
                                 [_ (error 'σ@ "no address ~a" (⟪α⟫->-α ⟪α⟫))])))])))

  

  (: σ@/list : (U -Σ -σ) -δσ (Listof ⟪α⟫) → (Listof -V^))
  ;; Look up store at address list
  (define (σ@/list Σ δσ ⟪α⟫s)
    (for/list ([α (in-list ⟪α⟫s)])
      (σ@ Σ δσ α)))

  (: defined-at? : (U -Σ -σ) -δσ ⟪α⟫ → Boolean)
  (define (defined-at? σ δσ α)
    (define (in? [m : (HashTable ⟪α⟫ -V^)])
      (match (hash-ref m α #f)
        [(? values V^) (not (∋ V^ -undefined))]
        [_ #f]))
    (or (in? δσ)
        (in? (if (-Σ? σ) (-Σ-σ σ) σ))))

  (define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.imm (-● ∅))))

  (: mutable? : ⟪α⟫ → Boolean)
  (define (mutable? ⟪α⟫)
    (match (⟪α⟫->-α ⟪α⟫)
      [(-α.x x _) (assignable? x)]
      [(-α.fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α.idx?) #t]
      [_ #f]))

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

  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Kontinuation store
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ⊥σₖ : -σₖ (hash))

  (: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -⟦k⟧))
  (define (σₖ@ m αₖ)
    (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ mk-∅))

  (: σₖ+! : -Σ -αₖ -⟦k⟧ → -αₖ)
  (define (σₖ+! Σ αₖ ⟦k⟧)
    (error 'TODO))
  )
