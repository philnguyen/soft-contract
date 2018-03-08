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
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-substructs -α (-α:opq))

(define-unit sto@
  (import val^)
  (export sto^)

  (define ⊥Σᵥ : Σᵥ (hasheq))
  (define ⊥Σₖ : Σₖ (hash))
  (define ⊥Σₐ : Σₐ (hash))

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

  (: Σₖ@ : (U Σ Σₖ) αₖ → Rt^)
  (define (Σₖ@ Σ αₖ) (hash-ref (->Σₖ Σ) αₖ mk-∅))

  (: Σₐ@ : (U Σ Σₐ) K → R^)
  (define (Σₐ@ Σ K) (hash-ref (->Σₐ Σ) K mk-∅))

  (define α• (mk-α (-α:opq)))

  (: defined-at? : (U Σ Σᵥ) α → Boolean)
  (define (defined-at? Σ α)
    (match (hash-ref (->Σᵥ Σ) α #f)
      [(? values V^) (not (∋ V^ -undefined))]
      [_ #f]))

  #|

  (: alloc : -Σ -φ ⟪α⟫ -V^ → -φ)
  (define (alloc Σ φ α V)
    (define σ (-Σ-σ Σ))
    (define δσ (-φ-cache φ))
    (define V*
      (case (cardinality σ δσ α)
        [(0) V]
        [(1) (V⊕ φ (hash-ref δσ α mk-∅) V)]
        [(N) (V⊕ φ (hash-ref  σ α mk-∅) V)]))
    (-φ (-φ-condition φ) (hash-set δσ α V*)))

  (: alloc* : -Σ -φ (Listof ⟪α⟫) (Listof -V^) → -φ)
  (define (alloc* Σ φ αs Vs)
    (for/fold ([φ : -φ φ]) ([α (in-list αs)] [V (in-list Vs)])
      (alloc Σ φ α V)))

  (: mut! : -Σ -φ ⟪α⟫ -V^ → -φ)
  (define (mut! Σ φ α V)
    (define σ (-Σ-σ Σ))
    (define δσ (-φ-cache φ))
    (case (cardinality σ δσ α)
      [(0 1) (-φ (-φ-condition φ) (hash-set δσ α V))]
      [(N) (define (upd [m : -σ]) (hash-update m α (λ ([V₀ : -V^]) (V⊕ φ V₀ V)) mk-∅))
           (set--Σ-σ! Σ (upd σ))
           (-φ (-φ-condition φ) (upd δσ))])) 

  (: mut*! : -Σ -φ (Listof ⟪α⟫) (Listof -V^) → -φ)
  (define (mut*! Σ φ αs Vs)
    (for/fold ([φ : -φ φ]) ([α (in-list αs)] [V (in-list Vs)])
      (mut! Σ φ α V)))

  (: bind-args : -Σ -ρ ℓ -H -φ -formals (Listof -V^) → (Values -ρ -φ))
  (define (bind-args Σ ρ ℓ H φ fml Vs)

    (: bind-init : -ρ -φ (Listof Symbol) (Listof -V^) → (Values -ρ -φ))
    (define (bind-init ρ φ xs Vs)
      (for/fold ([ρ : -ρ ρ] [φ : -φ φ])
                ([x (in-list xs)] [V (in-list Vs)])
        (define α (-α->⟪α⟫ (-α.x x H)))
        (values (hash-set ρ x α) (alloc Σ φ α V))))
    
    (match fml
      [(? list? xs) (bind-init ρ φ xs Vs)]
      [(-var xs xᵣ)
       (define-values (Vs-init Vs-rest) (split-at Vs (length xs)))
       (define-values (ρ₁ φ₁) (bind-init ρ φ xs Vs-init))
       (define-values (Vᵣ φ₂) (alloc-rest-args Σ ℓ H φ₁ Vs-rest))
       (define αᵣ (-α->⟪α⟫ (-α.x xᵣ H)))
       (values (ρ+ ρ₁ xᵣ αᵣ) (alloc Σ φ₂ αᵣ {set Vᵣ}))]))

  (: alloc-rest-args : ([-Σ ℓ -H -φ (Listof -V^)] [#:end -V] . ->* . (Values -V -φ)))
  (define (alloc-rest-args Σ ℓ H φ V^s #:end [tail -null])
    (let go ([V^s : (Listof -V^) V^s] [φ : -φ φ] [i : Natural 0])
      (match V^s
        ['() (values tail φ)]
        [(cons V^ V^s*)
         (define αₕ (-α->⟪α⟫ (-α.var-car ℓ H i)))
         (define αₜ (-α->⟪α⟫ (-α.var-cdr ℓ H i)))
         (define-values (Vₜ φₜ) (go V^s* φ (+ 1 i)))
         (define φ* (alloc Σ (alloc Σ φₜ αₕ V^) αₜ {set Vₜ}))
         (values (-Cons αₕ αₜ) φ*)])))

  

  

  (define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.imm (-● ∅))))

  

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

  (define ⊥σₐ : -σₐ (hasheq))

  (: σₐ⊕! : -Σ -φ -αₖ (Listof -V^) → (Listof -V^))
  (define (σₐ⊕! Σ φ αₖ Vs)
    (define σₐ (-Σ-σₐ Σ))
    (define-values (σₐ* Vs*) (σₐ⊕ Σ φ αₖ Vs))
    (set--Σ-σₐ! Σ σₐ*)
    Vs*)

  (: σₐ⊕ : -Σ -φ -αₖ (Listof -V^) → (Values -σₐ (Listof -V^)))
  (define (σₐ⊕ Σ φ αₖ Vs)
    (define n (length Vs))
    (match-define (-Σ σ _ σₐ _) Σ)
    (define As (hash-ref σₐ αₖ mk-∅))
    (define ?Vs₀
      (for/or : (Option (Listof -V^)) ([Vs₀ (in-set As)]
                                       #:when (= n (length Vs₀))
                                       #:when (andmap (λ ([V₁^ : -V^] [V₂^ : -V^])
                                                        (and (= 1 (set-count V₁^))
                                                             (= 1 (set-count V₂^))
                                                             (compat? φ (set-first V₁^) (set-first V₂^))))
                                                      Vs₀ Vs))
        Vs₀))
    (define Vs*
      (if ?Vs₀
          (for/list : (Listof -V^) ([V₀ (in-list ?Vs₀)] [V (in-list Vs)])
            (V⊕ φ V₀ V))
          Vs))
    (define σₐ* (hash-update σₐ αₖ
                             (λ ([As : (℘ (Listof -V^))]) (set-add As Vs*))
                             mk-∅))
    (values σₐ* Vs*))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Helpers
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (: cardinality : -σ -δσ ⟪α⟫ → Cardinality)
  (define (cardinality σ δσ ⟪α⟫)
    (define α (⟪α⟫->-α ⟪α⟫))
    (cond
      [(-𝒾? α) 1]
      [(-α.hv? α) 'N]
      [(hash-has-key? σ ⟪α⟫) 'N]
      [(hash-has-key? δσ ⟪α⟫) 1]
      [else 0]))

  (: cachable? : -σ -δσ ⟪α⟫ → Boolean)
  (define (cachable? σ δσ α)
    (equal? 1 (cardinality σ δσ α)))
  |#

  (: ->Σ (∀ (X) (Σ → X) → (U Σ X) → X))
  (define ((->Σ f) m) (if (Σ? m) (f m) m))
  (define ->Σᵥ (->Σ Σ-val))
  (define ->Σₖ (->Σ Σ-kon))
  (define ->Σₐ (->Σ Σ-evl))
  )
