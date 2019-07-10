#lang typed/racket/base

(provide mon@)

(require racket/set
         racket/list
         racket/match
         racket/vector
         (only-in racket/function curry)
         typed/racket/unit
         bnf
         set-extras
         unreachable
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(⟦C⟧ . ≜ . (Σ Ctx D → R))

(define-unit mon@
  (import static-info^
          cache^ val^ sto^ pretty-print^
          exec^ app^ gc^
          prover^)
  (export mon^)

  (define -FF {set -ff})
  (define x-mon (gensym 'mon_))

  (: mon : Σ Ctx D D → R)
  (define (mon Σ ctx C^ V^)
    (define args:root (D-root V^))
    (fold-ans (λ ([C : V])
                (define root (∪ (V-root C) args:root))
                (define Σ* (gc root Σ))
                (ref-$! ($:Key:Mon Σ* (current-MS) ctx C V^)
                        (λ () (gc-R root Σ* ((mon₁ C) Σ* ctx V^)))))
              (unpack C^ Σ)))

  (: mon* : Σ Ctx W W → R)
  (define (mon* Σ₀ ctx Cs Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (if (= (length Cs) (length Vs))
        (let loop ([ΔΣ : ΔΣ ⊥ΔΣ] [Σ : Σ Σ₀] [rev-As : W '()] [Cs : W Cs] [Vs : W Vs] [i : Natural 0])
          (match* (Cs Vs)
            [((cons C₁ Cs*) (cons V₁ Vs*))
             (define r₁ (mon Σ (Ctx-with-origin ctx (ℓ-with-id ℓₒ i)) C₁ V₁))
             (match (collapse-R Σ r₁)
               [(cons (app (curry collapse-W^ Σ) (app car A₁)) ΔΣ₁)
                (loop (⧺ ΔΣ ΔΣ₁) (⧺ Σ ΔΣ₁) (cons A₁ rev-As) Cs* Vs* (add1 i))]
               [#f ⊥R])]
            [('() '())
             (R-of (reverse rev-As) ΔΣ)]))
        (match-let ([(Ctx l+ _ ℓₒ ℓ) ctx])
          (err! (blm l+ ℓ ℓₒ Cs Vs))
          ⊥R)))

  (: mon₁ : V → ⟦C⟧)
  (define (mon₁ C)
    (cond [(Fn/C? C) (mon-Fn/C C)]
          [(St/C? C) (mon-St/C C)]
          [(X/C? C) (mon-X/C (X/C-_0 C))]
          [(And/C? C) (mon-And/C C)]
          [(Or/C? C) (mon-Or/C C)]
          [(Not/C? C) (mon-Not/C C)]
          [(One-Of/C? C) (mon-One-Of/C C)]
          [(Vectof/C? C) (mon-Vectof/C C)]
          [(Vect/C? C) (mon-Vect/C C)]
          [(Hash/C? C) (mon-Hash/C C)]
          [(Set/C? C) (mon-Set/C C)]
          [(Seal/C? C) (mon-Seal/C C)]
          [else (mon-Flat/C C)]))

  (: mon-Fn/C : Fn/C → ⟦C⟧)
  (define ((mon-Fn/C C) Σ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (with-split-Σ Σ 'procedure? (list Vs)
      (λ (W ΔΣ₁)
        (define arity-check (P:arity-includes (guard-arity C)))
        (with-split-Σ Σ arity-check W
          (match-lambda**
           [((list V*₀) _)
            (define V* (unpack V*₀ Σ))
            (define C:sig
              (let ([sig : (==>i → Fn/C-Sig)
                     (match-lambda
                       [(==>i doms rngs _)
                        (cons (var-map Dom-name doms) (and rngs (map Dom-name rngs)))])])
                (match C
                  [(? ==>i?) (sig C)]
                  [(∀/C xs _ _) (cons (-var xs #f) #f)]
                  [(Case-=> Cs) (map sig Cs)])))
            (define-values (αᵥ ΔΣ)
              (match V*
                ;; Reduce allocation for common case
                [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                [_ (define αᵥ (α:dyn (β:fn ctx C:sig) H₀))
                   (values αᵥ (alloc αᵥ V*))]))
            (R-of {set (Guarded (cons l+ l-) C αᵥ)} ΔΣ)])
          (λ (W _) (err! (blm l+ ℓₒ ℓ (list {set arity-check}) W))
             ⊥R)))
      (λ (W _) (err! (blm l+ ℓₒ ℓ (list {set 'procedure?}) W))
         ⊥R)))

  (: mon-St/C : St/C → ⟦C⟧)
  (define ((mon-St/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define-values (αₕ ℓₕ 𝒾) (St/C-fields C))
    (define S (Σ@/blob αₕ Σ₀))
    (define n (vector-length S))

    (: mon-St/C-fields : Σ D → R)
    (define (mon-St/C-fields Σ V)
      (let go ([i : Index 0] [Vs-rev : W '()] [ΔΣ : ΔΣ ⊥ΔΣ])
        (cond
          [(>= i n) (R-of (reverse Vs-rev) ΔΣ)]
          [else
           (define Σ⧺ΔΣ (⧺ Σ ΔΣ))
           (with-collapsing/R Σ⧺ΔΣ [(ΔΣ₀ Ws) (app Σ⧺ΔΣ ℓ {set (-st-ac 𝒾 i)} (list V))]
             (define ctx* (Ctx-with-origin ctx (ℓ-with-id ℓₕ i)))
             (define Cᵢ (vector-ref S i))
             (define Σ* (⧺ Σ⧺ΔΣ ΔΣ₀))
             (with-collapsing/R Σ* [(ΔΣ₁ Ws*) (mon Σ* ctx* Cᵢ (unpack (car (collapse-W^ Σ* Ws)) Σ*))]
               (go (assert (+ 1 i) index?)
                   (cons (car (collapse-W^ (⧺ Σ* ΔΣ₁) Ws*)) Vs-rev)
                   (⧺ ΔΣ ΔΣ₀ ΔΣ₁))))])))

    (with-split-Σ Σ₀ (-st-p 𝒾) (list Vs)
      (λ (W* ΔΣ)
        (with-collapsing/R Σ₀ [(ΔΣ* Ws) (mon-St/C-fields (⧺ Σ₀ ΔΣ) (car W*))]
          (define-values (Vₐ ΔΣₐ)
            (let* ([Σ₀⧺ΔΣ* (⧺ Σ₀ ΔΣ*)]
                   [W* (unpack-W (collapse-W^ Σ₀⧺ΔΣ* Ws) Σ₀⧺ΔΣ*)])
              (define α (α:dyn (β:st-elems ctx 𝒾) H₀))
              (values (St α ∅) (⧺ ΔΣ ΔΣ* (alloc α (list->vector W*))))))
          (if (struct-all-immutable? 𝒾)
              (R-of {set Vₐ} ΔΣₐ)
              (let ([α (α:dyn (β:st 𝒾 ctx) H₀)])
                (R-of {set (Guarded (cons l+ l-) C α)} (⧺ ΔΣₐ (alloc α {set Vₐ})))))))
      (λ (W* _) (err! (blm l+ ℓ ℓₒ (list {set C}) W*))
         ⊥R)))

  (: ?singleton-opaques : W → (Option (Listof (℘ P))))
  (define (?singleton-opaques W₀)
    (let go ([W : W W₀])
      (match W
        ['() '()]
        [(cons {singleton-set (-● Ps)} W*)
         (match (go W*)
           [(? values l) (cons Ps l)]
           [_ #f])]
        [_ #f])))

  (: mon-X/C : α → ⟦C⟧)
  ;; Need explicit contract reference to explicitly hint execution of loop
  (define ((mon-X/C α) Σ ctx V^) (mon Σ ctx (Σ@ α Σ) (unpack V^ Σ)))

  (: mon-And/C : And/C → ⟦C⟧)
  (define ((mon-And/C C) Σ ctx V^)
    (match-define (And/C α₁ α₂ ℓ) C)
    (with-collapsing/R Σ [(ΔΣ₁ Ws₁) (mon Σ (Ctx-with-origin ctx (ℓ-with-id ℓ 0)) (Σ@ α₁ Σ) V^)]
      (define Σ₁ (⧺ Σ ΔΣ₁))
      (match-define (list V^*) (collapse-W^ Σ₁ Ws₁))
      (ΔΣ⧺R ΔΣ₁ (mon Σ₁ (Ctx-with-origin ctx (ℓ-with-id ℓ 1)) (Σ@ α₂ Σ) V^*))))

  (: mon-Or/C : Or/C → ⟦C⟧)
  (define ((mon-Or/C C) Σ ctx V)
    (match-define (Or/C α₁ α₂ ℓ) C)

    (: chk : V^ V^ → R)
    (define (chk C-fo C-ho)
      (with-collapsing/R Σ
        [(ΔΣ Ws)
         (with-each-path ([(ΔΣ₁ W₁) (fc Σ (Ctx-origin ctx) C-fo V)])
           (match W₁
             [(list _) (R-of W₁ ΔΣ₁)]
             [(list V* _)
              (ΔΣ⧺R ΔΣ₁
                (mon (⧺ Σ ΔΣ₁) (Ctx-with-origin ctx (ℓ-with-id ℓ 1)) C-ho V*))]))]
        (R-of (collapse-W^ (⧺ Σ ΔΣ) Ws) ΔΣ)))
    (define C₁ (Σ@ α₁ Σ))
    (define C₂ (Σ@ α₂ Σ))
    (cond [(C^-flat? C₁ Σ) (chk C₁ C₂)]
          [(C^-flat? C₂ Σ) (chk C₂ C₁)]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")]))

  (: mon-Not/C : Not/C → ⟦C⟧)
  (define ((mon-Not/C C) Σ ctx V)
    (match-define (Not/C α _) C)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-each-path ([(ΔΣ W) (fc Σ ℓₒ (Σ@ α Σ) V)])
      (match W
        [(list Vs* _) (R-of Vs* ΔΣ)]
        [(list _) (err! (blm l+ ℓ ℓₒ (list {set C}) (list V)))
                  ⊥R])))

  (: mon-One-Of/C : One-Of/C → ⟦C⟧)
  (define ((mon-One-Of/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-split-Σ Σ C (list Vs)
      R-of
      (λ (W _) (err! (blm l+ ℓ ℓₒ (list {set C}) W))
         ⊥R)))

  (: mon-Vectof/C : Vectof/C → ⟦C⟧)
  (define ((mon-Vectof/C C) Σ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (with-split-Σ Σ 'vector? (list Vs)
      (λ (W* ΔΣ₀)
        (define V* (car W*))
        (match-define (Vectof/C αₕ ℓₕ) C)
        (define N (-● {set 'exact-nonnegative-integer?}))
        (define Σ₀ (⧺ Σ ΔΣ₀))
        (with-collapsing/R Σ₀ [(ΔΣ₁ Wₑs) (app Σ₀ ℓₒ {set 'vector-ref} (list V* {set N}))]
          (define Σ₁ (⧺ Σ₀ ΔΣ₁))
          (with-collapsing/R Σ₁ [(ΔΣ₂ _) (mon Σ₁ (Ctx-with-origin ctx (ℓ-with-id ℓₕ 'mon-VectOf/C)) (Σ@ αₕ Σ) (car (collapse-W^ Σ₁ Wₑs)))]
            (define-values (αᵥ ΔΣ*)
              (match V*
                [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                [_ (define αᵥ (α:dyn (β:unvct ctx) H₀))
                   (values αᵥ (alloc αᵥ V*))]))
            (R-of {set (Guarded (cons l+ l-) C αᵥ)} (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ ΔΣ*)))))
      (λ (W* _) (err! (blm l+ ℓₒ ℓ (list {set C}) W*))
         ⊥R)))

  (: mon-Vect/C : Vect/C → ⟦C⟧)
  (define ((mon-Vect/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define-values (αₕ ℓₕ n) (Vect/C-fields C))

    (: mon-fields : Σ D → R)
    (define (mon-fields Σ₀ Vs)
      (define Cs (Σ@/blob αₕ Σ₀))
      (define (ref [Σ : Σ] [i : Natural])
        (app Σ ℓₒ {set 'vector-ref} (list Vs {set (-b i)})))
      (let go ([i : Natural 0] [Σ : Σ Σ₀] [ΔΣ : ΔΣ ⊥ΔΣ])
        (if (>= i n)
            (R-of {set -void} ΔΣ)
            (with-collapsing/R Σ [(ΔΣ₀ Ws) (ref Σ i)]
              (define ctx* (Ctx-with-origin ctx (ℓ-with-id ℓₕ i)))
              (define Σ₁ (⧺ Σ ΔΣ₀))
              (define Cᵢ (vector-ref Cs i))
              (with-collapsing/R Σ₁ [(ΔΣ₁ Ws*) (mon Σ₁ ctx* Cᵢ (car (collapse-W^ Σ₁ Ws)))]
                (go (+ 1 i) (⧺ Σ₁ ΔΣ₁) (⧺ ΔΣ ΔΣ₀ ΔΣ₁)))))))

    (with-split-Σ Σ₀ 'vector? (list Vs)
      (λ (W* ΔΣ₁)
        (with-split-Σ Σ₀ (P:vec-len n) W*
          (λ (W* ΔΣ₂)
            (define V* (car W*))
            (define Σ₂ (⧺ Σ₀ ΔΣ₁ ΔΣ₂))
            (with-collapsing/R Σ₂ [(ΔΣ₃ _) (mon-fields Σ₂ V*)]
              (define-values (αᵥ ΔΣ*)
                (match V*
                  [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                  [_ (define αᵥ (α:dyn (β:unvct ctx) H₀))
                     (values αᵥ (alloc αᵥ V*))]))
              (R-of {set (Guarded (cons l+ l-) C αᵥ)} (⧺ ΔΣ₁ ΔΣ₂ ΔΣ₃ ΔΣ*))))
          (λ (W* _) (err! (blm l+ ℓ ℓₒ (list {set C}) W*))
             ⊥R)))
      (λ (W* _) (err! (blm l+ ℓ ℓₒ (list {set C}) W*))
         ⊥R)))

  (: mon-Hash/C : Hash/C → ⟦C⟧)
  (define ((mon-Hash/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (match-define (Hash/C αₖ αᵥ ℓₕ) C)

    (: chk-content : Σ V^ → R)
    (define (chk-content Σ Vs)
      (define dummy-ℓ (ℓ-with-src +ℓ₀ 'mon-hash/c))
      (define (chk-with [ac : Symbol] [αₚ : α])
        (define r
          (with-collapsing/R Σ [(ΔΣ Ws) (app Σ dummy-ℓ {set ac} (list Vs))]
            (define Σ* (⧺ Σ ΔΣ))
            (ΔΣ⧺R ΔΣ (mon Σ* (Ctx-with-origin ctx (ℓ-with-id ℓₕ ac)) (Σ@ αₚ Σ₀) (car (collapse-W^ Σ* Ws))))))
        (or (collapse-R/ΔΣ Σ r) ⊥ΔΣ))
      (define ΔΣ₁ (chk-with 'scv:hash-key αₖ))
      (define ΔΣ₂ (chk-with 'scv:hash-val αᵥ))
      (R-of {set -void} (ΔΣ⊔ Σ ΔΣ₁ ΔΣ₂)))

    (with-split-Σ Σ₀ 'hash? (list Vs)
      (λ (W* ΔΣ₀)
        (define Vᵤ (unpack (car W*) Σ₀))
        (with-collapsing/R Σ₀ [(ΔΣ₁ _) (chk-content (⧺ Σ₀ ΔΣ₀) Vᵤ)]
          (define αᵤ (α:dyn (β:unhsh ctx ℓₕ) H₀))
          (R-of {set (Guarded (cons l+ l-) C αᵤ)} (⧺ ΔΣ₀ ΔΣ₁ (alloc αᵤ Vᵤ)))))
      (λ (W* _) (err! (blm l+ ℓ ℓₒ (list {set C}) W*))
         ⊥R)))

  (: mon-Set/C : Set/C → ⟦C⟧)
  (define ((mon-Set/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (match-define (Set/C αₑ ℓₛ) C)

    (: chk-content : Σ V^ → R)
    (define (chk-content Σ Vs)
      (define dummy-ℓ (ℓ-with-src +ℓ₀ 'mon-set/c))
      (with-collapsing/R Σ [(ΔΣ Ws) (app Σ dummy-ℓ {set 'set-first} (list Vs))]
        (define Σ* (⧺ Σ ΔΣ))
        (ΔΣ⧺R ΔΣ (mon Σ* (Ctx-with-origin ctx (ℓ-with-id ℓₛ 'set-first)) (Σ@ αₑ Σ) (car (collapse-W^ Σ* Ws))))))

    (with-split-Σ Σ₀ 'set? (list Vs)
      (λ (W* ΔΣ₀)
        (define Vᵤ (unpack (car W*) Σ₀))
        (define Σ₁ (⧺ Σ₀ ΔΣ₀))
        (with-collapsing/R Σ₁ [(ΔΣ₁ _) (chk-content Σ₁ Vᵤ)]
          (define αᵤ (α:dyn (β:unset ctx ℓₛ) H₀))
          (R-of {set (Guarded (cons l+ l-) C αᵤ)} (⧺ ΔΣ₀ ΔΣ₁ (alloc αᵤ Vᵤ)))))
      (λ (W* _) (err! (blm l+ ℓ ℓₒ (list {set C}) W*))
         ⊥R)))

  (: mon-Seal/C : Seal/C → ⟦C⟧)
  (define ((mon-Seal/C C) Σ ctx V^*)
    (match-define (Seal/C α l) C)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define V^ (unpack V^* Σ))
    (cond
      ;; Seal position
      [(equal? l+ l) (R-of {set (Sealed α)} (alloc α V^))]
      ;; Unseal position
      [(equal? l- l)
       (define unsealed (Σ@ α Σ))
       (define ers (blm l+ ℓ ℓₒ (list {set C}) (list (set-remove V^ (Sealed α)))))
       ((inst fold-ans V)
        (match-lambda
          [(Sealed (== α)) (R-of unsealed)]
          [(? -●?) (R-of unsealed ⊥ΔΣ)]
          [_ (err! ers) ⊥R])
        V^)]
      [else !!!]))

  (: mon-Flat/C : V → ⟦C⟧)
  (define ((mon-Flat/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (define (blame) (blm l+ ℓ ℓₒ (list {set C}) (list Vs)))
    (case (sat Σ C Vs)
      [(✓) (R-of Vs)]
      [(✗) (err! (blame)) ⊥R]
      [else
       (with-each-path ([(ΔΣ W) (fc Σ ℓₒ {set C} Vs)])
         (match W
           [(list _) (R-of W ΔΣ)]
           [(list Vs* _) (err! (blame)) ⊥R]))]))

  ;; Can't get away with not having specialized flat-check procedure.
  ;; There's no straightforward way to fully refine a value by contract `c`
  ;; after applying `c` as a procedure (tricky when `c` is recursive and effectful)
  ;; Convention: `fc` returns:
  ;; - `[refine(v, c)   ]` if `v`          satisfies `c`
  ;; - `[refine(v,¬c),#f]` if `v` does not satisfies `c`,
  (: fc : Σ ℓ D D → R)
  (define (fc Σ₀ ℓ Cs Vs)
    (define Vs:root (D-root Vs))
    ((inst fold-ans V)
     (λ (C)
       (define root (∪ (V-root C) Vs:root))
       (define Σ₀* (gc root Σ₀))
       (ref-$! ($:Key:Fc Σ₀* (current-MS) ℓ C Vs)
               (λ () (gc-R root Σ₀* (fc₁ Σ₀* ℓ C Vs)))))
     (unpack Cs Σ₀)))

  (: fc₁ : Σ ℓ V D → R)
  (define (fc₁ Σ₀ ℓ C Vs)
    (match C
      [(And/C α₁ α₂ _)
       (with-collapsing/R Σ₀ [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (Σ@ α₁ Σ₀) Vs)]
         (for/fold ([r : R ⊥R]) ([W₁ (in-set Ws₁)])
           (match W₁
             [(list Vs*)
              (R⊔ r (ΔΣ⧺R ΔΣ₁ (fc (⧺ Σ₀ ΔΣ₁) ℓ (Σ@ α₂ Σ₀) Vs*)))]
             [(list _ _) (R⊔ r (R-of W₁ ΔΣ₁))])))]
      [(Or/C α₁ α₂ _)
       (with-collapsing/R Σ₀ [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (Σ@ α₁ Σ₀) Vs)]
         (for/fold ([r : R ⊥R]) ([W₁ (in-set Ws₁)])
           (match W₁
             [(list _) (R⊔ r (R-of W₁ ΔΣ₁))]
             [(list Vs* _)
              (define r₂ (fc (⧺ Σ₀ ΔΣ₁) ℓ (Σ@ α₂ Σ₀) Vs*))
              (R⊔ r (ΔΣ⧺R ΔΣ₁ r₂))])))]
      [(Not/C α _)
       (with-collapsing/R Σ₀ [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (Σ@ α Σ₀) Vs)]
         (for/fold ([r : R ⊥R]) ([W₁ (in-set Ws₁)])
           (R⊔ r (R-of (match W₁
                         [(list Vs*) (list Vs* -FF)]
                         [(list Vs* _) (list Vs*)])
                       ΔΣ₁))))]
      [(One-Of/C bs)
       (with-split-Σ Σ₀ (One-Of/C bs) (list Vs)
         R-of
         (λ (W ΔΣ) (R-of (list (car W) -FF) ΔΣ)))]
      [(? St/C? C)
       (define-values (αₕ _ 𝒾) (St/C-fields C))
       (define S (Σ@/blob αₕ Σ₀))
       (define n (vector-length S))
       (with-split-Σ Σ₀ (-st-p 𝒾) (list Vs)
         (λ (W* ΔΣ*)
           (define n (count-struct-fields 𝒾))
           (let go ([Σ : Σ Σ₀] [i : Index 0] [ΔΣ : ΔΣ ΔΣ*] [rev-W : W '()])
             (cond
               [(>= i n)
                (define α (α:dyn (β:st-elems ℓ 𝒾) H₀))
                (R-of {set (St α ∅)} (⧺ ΔΣ (alloc α (list->vector (unpack-W (reverse rev-W) Σ)))))]
               [else
                (define Cᵢ (vector-ref S i))
                (with-collapsing/R Σ [(ΔΣ:a Ws:a) (app Σ ℓ {set (-st-ac 𝒾 i)} W*)]
                  (define Σ* (⧺ Σ ΔΣ:a))
                  (with-each-path ([(ΔΣᵢ Wᵢ) (fc Σ* ℓ Cᵢ (car (collapse-W^ Σ* Ws:a)))])
                    (match Wᵢ
                      [(list Vᵢ)
                       (go (⧺ Σ ΔΣ:a ΔΣᵢ)
                           (assert (+ 1 i) index?)
                           (⧺ ΔΣ ΔΣ:a ΔΣᵢ) (cons Vᵢ rev-W))]
                      [(list Vᵢ _)
                       (define fields ((inst vector-append V^)
                                       (list->vector (unpack-W (reverse rev-W) Σ))
                                       (make-vector (- n i 1) {set (-● ∅)})))
                       (define α (α:dyn (β:st-elems ℓ 𝒾) H₀))
                       (R-of (list {set (St α ∅)} -FF) (⧺ ΔΣ:a ΔΣᵢ (alloc α fields)))])))])))
         (λ (W ΔΣ) (R-of (list (car W) -FF) ΔΣ)))]
      [(X/C α) (fc Σ₀ ℓ (Σ@ α Σ₀) (unpack Vs Σ₀))]
      [(and b (-b ub))
       (with-split-Σ Σ₀ 'equal? (list {set b} Vs)
         (λ (_ ΔΣ) (R-of {set b} ΔΣ))
         (λ (W ΔΣ)
           (define-values (V* ΔΣ*) (refine (cadr W) (P:¬ (P:≡ ub)) Σ₀))
           (R-of (list V* -FF) (⧺ ΔΣ ΔΣ*))))]
      [_
       (define ΔΣₓ (alloc-lex Σ₀ x-mon Vs))
       (define Σ₁ (⧺ Σ₀ ΔΣₓ))
       ;; FIXME instead of manually `resolve` like this, make the whole thing
       ;; more analogous to applying lamdbas
       (with-each-path ([(ΔΣ W) (app Σ₁ ℓ {set C} (list (resolve x-mon Σ₁)))])
         (define Σ₂ (⧺ Σ₁ ΔΣ))
         (define Vs* (Σ@ (γ:lex x-mon) Σ₂))
         (with-split-Σ Σ₂ 'values W
           (λ _ (R-of Vs* ΔΣ))
           (λ _ (R-of (list Vs* -FF) ΔΣ))))]))
  )
