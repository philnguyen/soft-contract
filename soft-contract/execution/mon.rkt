#lang typed/racket/base

(provide mon@)

(require racket/set
         racket/list
         racket/match
         racket/vector
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

(⟦C⟧ . ≜ . (Σ Ctx V^ → (Values R (℘ Err))))

(define-unit mon@
  (import static-info^
          cache^ val^ sto^ pretty-print^
          exec^ app^ gc^
          prover^)
  (export mon^)

  (define -FF {set -ff})
  (define γ-mon (γ:lex (gensym 'mon_)))

  (: mon : Σ Ctx V^ V^ → (Values R (℘ Err)))
  (define (mon Σ ctx C^ V^)
    (define args:root (V^-root V^))
    (fold-ans (λ ([C : V])
                (define root (∪ (V-root C) args:root))
                (define Σ* (gc root Σ))
                (ref-$! ($:Key:Mon Σ* ctx C V^)
                        (λ () (with-gc root Σ* (λ () ((mon₁ C) Σ* ctx V^))))))
              (unpack C^ Σ)))

  (: mon* : Σ Ctx W W → (Values R (℘ Err)))
  (define (mon* Σ₀ ctx Cs Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (if (= (length Cs) (length Vs))
        (let loop ([ΔΣ : ΔΣ ⊥ΔΣ] [Σ : Σ Σ₀] [rev-As : W '()] [es : (℘ Err) ∅] [Cs : W Cs] [Vs : W Vs] [i : Natural 0])
          (match* (Cs Vs)
            [((cons C₁ Cs*) (cons V₁ Vs*))
             (define-values (r₁ es₁) (mon Σ (Ctx-with-origin ctx (ℓ-with-id ℓₒ i)) C₁ V₁))
             (match (collapse-R r₁)
               [(cons (app collapse-W^ (app car A₁)) ΔΣ₁)
                (loop (⧺ ΔΣ ΔΣ₁) (⧺ Σ ΔΣ₁) (cons A₁ rev-As) (∪ es es₁) Cs* Vs* (add1 i))]
               [#f (values ⊥R (∪ es es₁))])]
            [('() '())
             (values (R-of (reverse rev-As) ΔΣ) es)]))
        (match-let ([(Ctx l+ _ ℓₒ ℓ) ctx])
          (err (blm l+ ℓ ℓₒ Cs Vs)))))

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
           [((list V*) ΔΣ₂)
            (define C:sig
              (let ([sig : (==>i → Fn/C-Sig)
                     (match-lambda
                       [(==>i doms rngs)
                        (cons (var-map Dom-name doms) (and rngs (map Dom-name rngs)))])])
                (match C
                  [(? ==>i?) (sig C)]
                  [(∀/C xs _ _ _) (cons (-var xs #f) #f)]
                  [(Case-=> Cs) (map sig Cs)])))
            (define-values (αᵥ ΔΣ)
              (match V*
                ;; Reduce allocation for common case
                [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                [_ (define αᵥ (α:dyn (β:fn ctx C:sig) H₀))
                   (values αᵥ (alloc αᵥ V*))]))
            (just (Guarded (cons l+ l-) C αᵥ) ΔΣ)])
          (λ (W _) (err (blm l+ ℓₒ ℓ (list {set arity-check}) W)))))
      (λ (W _) (err (blm l+ ℓₒ ℓ (list {set 'procedure?}) W)))))

  (: mon-St/C : St/C → ⟦C⟧)
  (define ((mon-St/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define-values (αₕ ℓₕ 𝒾) (St/C-fields C))
    (define S (Σ@/blob αₕ Σ₀))
    (define n (vector-length S))

    (: mon-St/C-fields : Σ V^ → (Values R (℘ Err)))
    (define (mon-St/C-fields Σ V)
      (let go ([i : Index 0] [Vs-rev : W '()] [ΔΣ : ΔΣ ⊥ΔΣ])
        (cond
          [(>= i n) (just (reverse Vs-rev) ΔΣ)]
          [else
           (with-collapsing/R [(ΔΣ₀ Ws) (app (⧺ Σ ΔΣ) ℓ {set (-st-ac 𝒾 i)} (list V))]
             (define ctx* (Ctx-with-origin ctx (ℓ-with-id ℓₕ i)))
             (define Cᵢ (vector-ref S i))
             (with-collapsing/R [(ΔΣ₁ Ws*) (mon (⧺ Σ ΔΣ ΔΣ₀) ctx* Cᵢ (car (collapse-W^ Ws)))]
               (go (assert (+ 1 i) index?)
                   (cons (car (collapse-W^ Ws*)) Vs-rev)
                   (⧺ ΔΣ ΔΣ₀ ΔΣ₁))))])))

    (with-split-Σ Σ₀ (-st-p 𝒾) (list Vs)
      (λ (W* ΔΣ)
        (with-collapsing/R [(ΔΣ* Ws) (mon-St/C-fields (⧺ Σ₀ ΔΣ) (car W*))]
          (define-values (Vₐ ΔΣₐ)
            (match (collapse-W^ Ws)
              ;; Reduce allocation in common case
              [(app ?singleton-opaques (? values l))
               (define Ps
                 (set-add
                  (for/union : (℘ P) ([(Psᵢ i) (in-indexed l)])
                    (map/set (λ ([P : P]) (P:St (list (-st-ac 𝒾 (assert i index?))) P))
                             Psᵢ))
                  (-st-p 𝒾)))
               (values (-● Ps) (⧺ ΔΣ ΔΣ*))]
              [W*
               (define α (α:dyn (β:st-elems ctx 𝒾) H₀))
               (values (St α ∅) (⧺ ΔΣ ΔΣ* (alloc α (list->vector W*))))]))
          (if (struct-all-immutable? 𝒾)
              (just Vₐ ΔΣₐ)
              (let ([α (α:dyn (β:st 𝒾 ctx) H₀)])
                (just (Guarded (cons l+ l-) C α) (⧺ ΔΣₐ (alloc α {set Vₐ})))))))
      (λ (W* _) (err (blm l+ ℓ ℓₒ (list {set C}) W*)))))

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
  (define ((mon-X/C α) Σ ctx V^) (mon Σ ctx (unpack α Σ) (unpack V^ Σ)))

  (: mon-And/C : And/C → ⟦C⟧)
  (define ((mon-And/C C) Σ ctx V^)
    (match-define (And/C α₁ α₂ ℓ) C)
    (with-collapsing/R [(ΔΣ₁ Ws₁) (mon Σ (Ctx-with-origin ctx (ℓ-with-id ℓ 0)) (Σ@ α₁ Σ) V^)]
      (match-define (list V^*) (collapse-W^ Ws₁))
      (with-pre ΔΣ₁ (mon (⧺ Σ ΔΣ₁) (Ctx-with-origin ctx (ℓ-with-id ℓ 1)) (Σ@ α₂ Σ) V^*))))

  (: mon-Or/C : Or/C → ⟦C⟧)
  (define ((mon-Or/C C) Σ ctx V)
    (match-define (Or/C α₁ α₂ ℓ) C)

    (: chk : V^ V^ → (Values R (℘ Err)))
    (define (chk C-fo C-ho)
      (with-collapsing/R
        [(ΔΣ Ws)
         (with-each-ans ([(ΔΣ₁ W₁) (fc Σ (Ctx-origin ctx) C-fo V)])
           (match W₁
             [(list _) (just W₁ ΔΣ₁)]
             [(list V* _)
              (with-pre ΔΣ₁
                (mon (⧺ Σ ΔΣ₁) (Ctx-with-origin ctx (ℓ-with-id ℓ 1)) C-ho V*))]))]
        (just (collapse-W^ Ws) ΔΣ)))
    (define C₁ (Σ@ α₁ Σ))
    (define C₂ (Σ@ α₂ Σ))
    (cond [(C^-flat? C₁ Σ) (chk C₁ C₂)]
          [(C^-flat? C₂ Σ) (chk C₂ C₁)]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")]))

  (: mon-Not/C : Not/C → ⟦C⟧)
  (define ((mon-Not/C C) Σ ctx V)
    (match-define (Not/C α _) C)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-each-ans ([(ΔΣ W) (fc Σ ℓₒ (Σ@ α Σ) V)])
      (match W
        [(list Vs* _) (just Vs* ΔΣ)]
        [(list _) (err (blm l+ ℓ ℓₒ (list {set C}) (list V)))])))

  (: mon-One-Of/C : One-Of/C → ⟦C⟧)
  (define ((mon-One-Of/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-split-Σ Σ C (list Vs)
      just
      (λ (W _) (err (blm l+ ℓ ℓₒ (list {set C}) W)))))

  (: mon-Vectof/C : Vectof/C → ⟦C⟧)
  (define ((mon-Vectof/C C) Σ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (with-split-Σ Σ 'vector? (list Vs)
      (λ (W* ΔΣ₀)
        (define V* (car W*))
        (match-define (Vectof/C αₕ ℓₕ) C)
        (define N (-● {set 'exact-nonnegative-integer?}))
        (define Σ₀ (⧺ Σ ΔΣ₀))
        (with-collapsing/R [(ΔΣ₁ Wₑs) (app Σ₀ ℓₒ {set 'vector-ref} (list V* {set N}))]
          (with-collapsing/R [(ΔΣ₂ _) (mon (⧺ Σ₀ ΔΣ₁) (Ctx-with-origin ctx (ℓ-with-id ℓₕ 'mon-VectOf/C)) (Σ@ αₕ Σ) (car (collapse-W^ Wₑs)))]
            (define-values (αᵥ ΔΣ*)
              (match V*
                [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                [_ (define αᵥ (α:dyn (β:unvct ctx) H₀))
                   (values αᵥ (alloc αᵥ V*))]))
            (just (Guarded (cons l+ l-) C αᵥ) (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ ΔΣ*)))))
      (λ (W* _) (err (blm l+ ℓₒ ℓ (list {set C}) W*)))))

  (: mon-Vect/C : Vect/C → ⟦C⟧)
  (define ((mon-Vect/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define-values (αₕ ℓₕ n) (Vect/C-fields C))

    (: mon-fields : Σ V^ → (Values R (℘ Err)))
    (define (mon-fields Σ₀ Vs)
      (define Cs (Σ@/blob αₕ Σ₀))
      (define (ref [Σ : Σ] [i : Natural])
        (app Σ ℓₒ {set 'vector-ref} (list Vs {set (-b i)})))
      (let go ([i : Natural 0] [Σ : Σ Σ₀] [ΔΣ : ΔΣ ⊥ΔΣ])
        (if (>= i n)
            (just -void ΔΣ)
            (with-collapsing/R [(ΔΣ₀ Ws) (ref Σ i)]
              (define ctx* (Ctx-with-origin ctx (ℓ-with-id ℓₕ i)))
              (define Σ₁ (⧺ Σ ΔΣ₀))
              (define Cᵢ (vector-ref Cs i))
              (with-collapsing/R [(ΔΣ₁ Ws*) (mon Σ₁ ctx* Cᵢ (car (collapse-W^ Ws)))]
                (go (+ 1 i) (⧺ Σ₁ ΔΣ₁) (⧺ ΔΣ ΔΣ₀ ΔΣ₁)))))))

    (with-split-Σ Σ₀ 'vector? (list Vs)
      (λ (W* ΔΣ₁)
        (with-split-Σ Σ₀ (P:vec-len n) W*
          (λ (W* ΔΣ₂)
            (define V* (car W*))
            (with-collapsing/R [(ΔΣ₃ _) (mon-fields (⧺ Σ₀ ΔΣ₁ ΔΣ₂) V*)]
              (define-values (αᵥ ΔΣ*)
                (match V*
                  [{singleton-set (? -●? V)} (values (γ:imm V) ⊥ΔΣ)]
                  [_ (define αᵥ (α:dyn (β:unvct ctx) H₀))
                     (values αᵥ (alloc αᵥ V*))]))
              (just (Guarded (cons l+ l-) C αᵥ) (⧺ ΔΣ₁ ΔΣ₂ ΔΣ₃ ΔΣ*))))
          (λ (W* _) (err (blm l+ ℓ ℓₒ (list {set C}) W*)))))
      (λ (W* _) (err (blm l+ ℓ ℓₒ (list {set C}) W*)))))

  (: mon-Hash/C : Hash/C → ⟦C⟧)
  (define ((mon-Hash/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (match-define (Hash/C αₖ αᵥ ℓₕ) C)

    (: chk-content : Σ V^ → (Values R (℘ Err)))
    (define (chk-content Σ Vs)
      (define dummy-ℓ (ℓ-with-src +ℓ₀ 'mon-hash/c))
      (define (chk-with [ac : Symbol] [αₚ : α])
        (define-values (r es)
          (with-collapsing/R [(ΔΣ Ws) (app Σ dummy-ℓ {set ac} (list Vs))]
            (with-pre ΔΣ (mon (⧺ Σ ΔΣ) (Ctx-with-origin ctx (ℓ-with-id ℓₕ ac)) (Σ@ αₚ Σ₀) (car (collapse-W^ Ws))))))
        (values (or (collapse-R/ΔΣ r) ⊥ΔΣ) es))
      (define-values (ΔΣ₁ es₁) (chk-with 'scv:hash-key αₖ))
      (define-values (ΔΣ₂ es₂) (chk-with 'scv:hash-val αᵥ))
      (values (R-of -void (ΔΣ⊔ ΔΣ₁ ΔΣ₂)) (∪ es₁ es₂)))

    (with-split-Σ Σ₀ 'hash? (list Vs)
      (λ (W* ΔΣ₀)
        (define Vᵤ (unpack (car W*) Σ₀))
        (with-collapsing/R [(ΔΣ₁ _) (chk-content (⧺ Σ₀ ΔΣ₀) Vᵤ)]
          (define αᵤ (α:dyn (β:unhsh ctx ℓₕ) H₀))
          (just (Guarded (cons l+ l-) C αᵤ) (⧺ ΔΣ₀ ΔΣ₁ (alloc αᵤ Vᵤ)))))
      (λ (W* _) (err (blm l+ ℓ ℓₒ (list {set C}) W*)))))

  (: mon-Set/C : Set/C → ⟦C⟧)
  (define ((mon-Set/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (match-define (Set/C αₑ ℓₛ) C)

    (: chk-content : Σ V^ → (Values R (℘ Err)))
    (define (chk-content Σ Vs)
      (define dummy-ℓ (ℓ-with-src +ℓ₀ 'mon-set/c))
      (with-collapsing/R [(ΔΣ Ws) (app Σ dummy-ℓ {set 'set-first} (list Vs))]
        (with-pre ΔΣ (mon (⧺ Σ ΔΣ) (Ctx-with-origin ctx (ℓ-with-id ℓₛ 'set-first)) (Σ@ αₑ Σ) (car (collapse-W^ Ws))))))

    (with-split-Σ Σ₀ 'set? (list Vs)
      (λ (W* ΔΣ₀)
        (define Vᵤ (unpack (car W*) Σ₀))
        (with-collapsing/R [(ΔΣ₁ _) (chk-content (⧺ Σ₀ ΔΣ₀) Vᵤ)]
          (define αᵤ (α:dyn (β:unset ctx ℓₛ) H₀))
          (just (Guarded (cons l+ l-) C αᵤ) (⧺ ΔΣ₀ ΔΣ₁ (alloc αᵤ Vᵤ)))))
      (λ (W* _) (err (blm l+ ℓ ℓₒ (list {set C}) W*)))))

  (: mon-Seal/C : Seal/C → ⟦C⟧)
  (define ((mon-Seal/C C) Σ ctx V^*)
    (match-define (Seal/C α l) C)
    (match-define (Ctx l+ l- ℓₒ ℓ) ctx)
    (define V^ (unpack V^* Σ))
    (cond
      ;; Seal position
      [(equal? l+ l) (just (Sealed α) (alloc α V^))]
      ;; Unseal position
      [(equal? l- l)
       (define unsealed (Σ@ α Σ))
       (define ers (blm l+ ℓ ℓₒ (list {set C}) (list (set-remove V^ (Sealed α)))))
       ((inst fold-ans V)
        (match-lambda
          [(Sealed (== α)) (just unsealed)]
          [(? -●?) (values (R-of unsealed ⊥ΔΣ) ers)]
          [_ (err ers)])
        V^)]
      [else !!!]))

  (: mon-Flat/C : V → ⟦C⟧)
  (define ((mon-Flat/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (define (blame) (blm l+ ℓ ℓₒ (list {set C}) (list Vs)))
    (case (sat Σ C Vs)
      [(✓) (just Vs)]
      [(✗) (err (blame))]
      [else
       (with-each-ans ([(ΔΣ W) (fc Σ ℓₒ {set C} Vs)])
         (match W
           [(list _) (just W ΔΣ)]
           [(list Vs* _) (err (blame))]))]))

  ;; Can't get away with not having specialized flat-check procedure.
  ;; There's no straightforward way to fully refine a value by contract `c`
  ;; after applying `c` as a procedure (tricky when `c` is recursive and effectful)
  ;; Convention: `fc` returns:
  ;; - `[refine(v, c)   ]` if `v`          satisfies `c`
  ;; - `[refine(v,¬c),#f]` if `v` does not satisfies `c`,
  (: fc : Σ ℓ V^ V^ → (Values R (℘ Err)))
  (define (fc Σ₀ ℓ Cs Vs)
    (define Vs:root (V^-root Vs))
    ((inst fold-ans V)
     (λ (C)
       (define root (∪ (V-root C) Vs:root))
       (define Σ₀* (gc root Σ₀))
       (ref-$! ($:Key:Fc Σ₀* ℓ C Vs)
               (λ () (with-gc root Σ₀* (λ () (fc₁ Σ₀* ℓ C Vs))))))
     Cs))

  (: fc₁ : Σ ℓ V V^ → (Values R (℘ Err)))
  (define (fc₁ Σ₀ ℓ C Vs)
    (match C
      [(And/C α₁ α₂ _)
       (with-collapsing/R [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (unpack α₁ Σ₀) Vs)]
         (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([W₁ (in-set Ws₁)])
           (match W₁
             [(list Vs*)
              (define-values (r₂ es₂) (fc (⧺ Σ₀ ΔΣ₁) ℓ (unpack α₂ Σ₀) Vs*))
              (values (R⊔ r (ΔΣ⧺R ΔΣ₁ r₂)) (∪ es es₂))]
             [(list _ _) (values (R⊔ r (R-of W₁ ΔΣ₁)) es)])))]
      [(Or/C α₁ α₂ _)
       (with-collapsing/R [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (unpack α₁ Σ₀) Vs)]
         (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([W₁ (in-set Ws₁)])
           (match W₁
             [(list _) (values (R⊔ r (R-of W₁ ΔΣ₁)) es)]
             [(list Vs* _)
              (define-values (r₂ es₂) (fc (⧺ Σ₀ ΔΣ₁) ℓ (unpack α₂ Σ₀) Vs*))
              (values (R⊔ r (ΔΣ⧺R ΔΣ₁ r₂)) (∪ es es₂))])))]
      [(Not/C α _)
       (with-collapsing/R [(ΔΣ₁ Ws₁) (fc Σ₀ ℓ (unpack α Σ₀) Vs)]
         (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([W₁ (in-set Ws₁)])
           (values (R⊔ r (R-of (match W₁
                                 [(list Vs*) (list Vs* -FF)]
                                 [(list Vs* _) (list Vs*)])
                               ΔΣ₁))
                   es)))]
      [(One-Of/C bs)
       (with-split-Σ Σ₀ (One-Of/C bs) (list Vs)
         just
         (λ (W ΔΣ) (just (list (car W) -FF) ΔΣ)))]
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
                (just (St α ∅) (⧺ ΔΣ (alloc α (list->vector (reverse rev-W)))))]
               [else
                (define Cᵢ (vector-ref S i))
                (with-collapsing/R [(ΔΣ:a Ws:a) (app Σ ℓ {set (-st-ac 𝒾 i)} W*)]
                  (with-each-ans ([(ΔΣᵢ Wᵢ) (fc (⧺ Σ ΔΣ:a) ℓ Cᵢ (car (collapse-W^ Ws:a)))])
                    (match Wᵢ
                      [(list Vᵢ)
                       (go (⧺ Σ ΔΣ:a ΔΣᵢ)
                           (assert (+ 1 i) index?)
                           (⧺ ΔΣ ΔΣ:a ΔΣᵢ) (cons Vᵢ rev-W))]
                      [(list Vᵢ _)
                       (define fields ((inst vector-append V^)
                                       (list->vector (reverse rev-W))
                                       (make-vector (- n i 1) {set (-● ∅)})))
                       (define α (α:dyn (β:st-elems ℓ 𝒾) H₀))
                       (just (list {set (St α ∅)} -FF) (⧺ ΔΣ:a ΔΣᵢ (alloc α fields)))])))])))
         (λ (W ΔΣ) (just (list (car W) -FF) ΔΣ)))]
      [(X/C α) (fc Σ₀ ℓ (unpack α Σ₀) (unpack Vs Σ₀))]
      [(? -b? b)
       (with-split-Σ Σ₀ 'equal? (list {set b} Vs)
         (λ (_ ΔΣ) (just b ΔΣ))
         (λ (W ΔΣ)
           (define-values (V* ΔΣ*) (refine (cadr W) (P:¬ (P:≡ b)) Σ₀))
           (just (list V* -FF) (⧺ ΔΣ ΔΣ*))))]
      [_
       (define ΔΣₓ (alloc γ-mon Vs))
       (with-each-ans ([(ΔΣ W) (app (⧺ Σ₀ ΔΣₓ) ℓ {set C} (list {set γ-mon}))])
         (define Σ₁ (⧺ Σ₀ ΔΣₓ ΔΣ))
         (define Vs* (unpack γ-mon Σ₁))
         (with-split-Σ Σ₁ 'values W
           (λ _ (just Vs* ΔΣ))
           (λ _ (just (list Vs* -FF) ΔΣ))))]))
  )
