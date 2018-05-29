#lang typed/racket/base

(provide mon@)

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         typed/racket/unit
         set-extras
         bnf
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit mon@
  (import static-info^ meta-functions^
          val^ env^ evl^ sto^
          prover^
          prims^
          step^ app^ compile^ fc^ approx^ alloc^)
  (export mon^)

  (⟦C⟧ . ≜ . (T^ Ctx Φ^ Ξ:co Σ → (℘ Ξ)))

  (: mon : T^ T^ Ctx Φ^ Ξ:co Σ → (℘ Ξ))
  (define (mon C^ T^ ctx Φ^ Ξ₀ Σ)
    (for/union : (℘ Ξ) ([C (in-set (T->V Σ Φ^ C^))])
      ((mon₁ C) T^ ctx Φ^ Ξ₀ Σ)))

  (: mon₁ : V → ⟦C⟧)
  (define (mon₁ C)
    (cond [(Fn/C? C) (mon-Fn/C C)]
          [(St/C? C) (mon-St/C C)]
          [(X/C? C) (mon-X/C C)]
          [(And/C? C) (mon-And/C C)]
          [(Or/C? C) (mon-Or/C C)]
          [(Not/C? C) (mon-Not/C C)]
          [(One-Of/C? C) (mon-One-Of/C C)]
          [(Vectof? C) (mon-Vectof C)]
          [(Vect/C? C) (mon-Vect/C C)]
          [(Hash/C? C) (mon-Hash/C C)]
          [(Set/C? C) (mon-Set/C C)]
          [(Seal/C? C) (mon-Seal/C C)]
          [else (mon-Flat/C C)]))

  (: mon-Fn/C : Fn/C → ⟦C⟧)
  (define ((mon-Fn/C C) T^₀ ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (define C:arity (guard-arity C))
    
    (define (chk-arity [R^ : R^])
      (cond
        [C:arity
         (define grd-arity (-b C:arity))
         (for/union : (℘ Ξ) ([Rᵢ (in-set R^)])
           (match-define (R (list Tₕ) Φ^ᵢ) Rᵢ)
           (define Tₕ:arity
             (cond [(set? Tₕ) (for/set : V^ ([Vᵢ (in-set Tₕ)])
                                (cond [(T-arity Vᵢ) => -b]
                                      [else (-● {set 'procedure-arity?})]))]
                   [(and (S? Tₕ) (T-arity Tₕ)) => -b]
                   [else (S:@ 'procedure-arity (list Tₕ))]))
           ((inst with-2-paths Ξ)
             (λ () (split-results Σ (R (list Tₕ:arity grd-arity) Φ^ᵢ) 'arity-includes?))
             (λ (R^)
               (wrap {set (R (list Tₕ) (set-union-map R-_1 R^))}))
             (λ _
               (define C (match C:arity
                           [(? integer? n)
                            (format-symbol "(arity-includes/c ~a)" n)]
                           [(arity-at-least k)
                            (format-symbol "(arity-at-least/c ~a)" k)]
                           [(list k ...)
                            (string->symbol (format "(arity-one-of/c ~a)" k))]))
               (blm (ℓ-with-src ℓ l+) lₒ (list {set C}) (list Tₕ)))))]
        [else (wrap R^)]))

    (define (wrap [R^ : R^])
      (: go : Arity → (℘ Ξ:co))
      (define (go a)
        (define α (mk-α (-α:fn ctx (Ξ:co-ctx Ξ₀) a)))
        (define V* (V^+ Σ (V^+ Σ (R->V Σ R^) 'procedure?) (P:arity-includes a)))
        (⊔ᵥ! Σ α V*)
        {set (ret! (T->R (X/G ctx C α) (collapse-R^/Φ^ R^)) Ξ₀ Σ)})
      (if C:arity
          (go C:arity)
          (match (for/set : (℘ Arity) ([V (in-set (R->V Σ R^))])
                   (assert (T-arity V)))
            [{singleton-set a} (go a)])))
    
    (with-check Σ Φ^₀ ctx T^₀ 'procedure? (if (∀/C? C) wrap chk-arity)))

  (: mon-St/C : St/C → ⟦C⟧)
  (define ((mon-St/C C) T^₀ ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (St/C _ 𝒾 αℓs) C)
    (with-check Σ Φ^₀ ctx T^₀ (-st-p 𝒾)
      (λ (R^)
        (define-values (T^ Φ^) (collapse-R^-1 Σ R^))
        (define ⟦mon⟧s : (Listof ⟦E⟧)
          (for/list ([αℓᵢ (in-list αℓs)] [i (in-naturals)] #:when (index? i))
            (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
            (define ⟦Vᵢ⟧ (let ([ℓ* (ℓ-with-id ℓ (list 'mon-struct/c 𝒾 i))])
                           (mk-app ℓ* (mk-T (-st-ac 𝒾 i)) (list (mk-T T^)))))
            (mk-mon (Ctx-with-ℓ ctx ℓᵢ) (mk-T (Σᵥ@ Σ αᵢ)) ⟦Vᵢ⟧)))
        (define ⟦reconstr⟧ (mk-app ℓ (mk-T (-st-mk 𝒾)) ⟦mon⟧s))
        (define Ξ* (cond [(struct-all-immutable? 𝒾) Ξ₀]
                         [else (K+ (F:Wrap C ctx (mk-α (-α:st 𝒾 ctx (Ξ:co-ctx Ξ₀)))) Ξ₀)]))
        {set (⟦reconstr⟧ ⊥Ρ Φ^ Ξ* Σ)})))

  (: mon-X/C : X/C → ⟦C⟧)
  (define ((mon-X/C C) V ctx Φ^ Ξ Σ)
    (match-define (Ξ:co (K _ (αₖ H _)) ?m) Ξ)
    (match-define (X/C α) C)
    (define H* (H+ H (Ctx-loc ctx) C))
    (define α* (αₖ H* (βₖ:mon ctx α)))
    (⊔ₖ! Σ α* (Rt Φ^ {seteq α} Ξ))
    (match-define (-α:x/c x _) (inspect-α α))
    (define-values (Φ^* Ρ) (bind-args! Φ^ ⊥Ρ (-var (list x) #f) (list V) H* Σ))
    (define Ξ* (Ξ:co (K (list (F:Mon:C ctx (Σᵥ@ Σ α))) α*) ?m))
    {set (ret! (R (list (S:α (hash-ref Ρ x))) Φ^*) Ξ* Σ)})

  (: mon-And/C : And/C → ⟦C⟧)
  (define ((mon-And/C C) V ctx Φ^ Ξ Σ)
    (match-define (And/C _ αℓ₁ αℓ₂) C)
    (define-values (C₁ ctx₁) (Σᵥ@/ctx Σ ctx αℓ₁))
    (define-values (C₂ ctx₂) (Σᵥ@/ctx Σ ctx αℓ₂))
    (define Ξ* (K+ (F:Mon:C ctx₁ C₁) (K+ (F:Mon:C ctx₂ C₂) Ξ)))
    {set (ret! (T->R V Φ^) Ξ* Σ)})

  (: mon-Or/C : Or/C → ⟦C⟧)
  (define ((mon-Or/C C) V ctx Φ^ Ξ₀ Σ)
    (match-define (Or/C flat? αℓ₁ αℓ₂) C)

    (: chk : V^ Ctx V^ Ctx → (℘ Ξ))
    (define (chk C-fl ctx-fl C-ho ctx-ho)
      (match-define (Ctx _ _ lₒ-fl ℓ-fl) ctx-fl)
      (define Ξ* (K+ (F:Mon-Or/C ctx-ho C-fl C-ho V) Ξ₀))
      (fc C-fl V (ℓ-with-src ℓ-fl lₒ-fl) Φ^ Ξ* Σ))

    (define-values (C₁ ctx₁) (Σᵥ@/ctx Σ ctx αℓ₁))
    (define-values (C₂ ctx₂) (Σᵥ@/ctx Σ ctx αℓ₂))
    (cond [(C^-flat? C₁) (chk C₁ ctx₁ C₂ ctx₂)]
          [(C^-flat? C₂) (chk C₂ ctx₂ C₁ ctx₁)]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")]))

  (: mon-Not/C : Not/C → ⟦C⟧)
  (define ((mon-Not/C C) V ctx Φ^ Ξ Σ)
    (match-define (Ctx l+ _ lₒ ℓₘ) ctx)
    (match-define (Not/C (αℓ α ℓ)) C)
    (define C* (Σᵥ@ Σ α))
    (define Ξ*
      (let ([⟦ok⟧ (mk-W (list V))]
            [⟦er⟧ (mk-Blm (Blm (ℓ-with-src ℓₘ l+) lₒ (list {set C}) (list V)))])
        (K+ (F:If lₒ ⟦er⟧ ⟦ok⟧ ⊥Ρ) Ξ)))
    (app C* (list V) ℓ Φ^ Ξ* Σ))

  (: mon-One-Of/C : One-Of/C → ⟦C⟧)
  (define ((mon-One-Of/C C) V ctx Φ^ Ξ Σ)
    (match-define (One-Of/C bs) C)
    (define (er) (match-let ([(Ctx l+ _ lo ℓ) ctx])
                   (blm (ℓ-with-src ℓ l+) lo (list C) (list V))))
    (case (check-one-of Φ^ V bs)
      [(✓) {set (ret! (T->R V Φ^) Ξ Σ)}]
      [(✗) (er)]
      [else (set-add (er) (ret! (T->R (list->set (map -b bs)) Φ^) Ξ Σ))]))

  (: mon-Vectof : Vectof → ⟦C⟧)
  (define ((mon-Vectof C) V ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (Vectof (αℓ α* ℓ*)) C)
    (with-check Σ Φ^₀ ctx V 'vector?
      (λ (R^)
        (define-values (T^ Φ^) (collapse-R^-1 Σ R^))
        (define ⟦elem⟧
          (let ([ℓ* (ℓ-with-id ℓ '(mon-vectorof))]
                [Idx (mk-T (-● {set 'exact-nonnegative-integer?}))])
            (mk-app ℓ* (mk-T 'vector-ref) (list (mk-T T^) Idx))))
        (define ⟦mon⟧ (mk-mon (Ctx-with-ℓ ctx ℓ*) (mk-T (Σᵥ@ Σ α*)) ⟦elem⟧))
        (define Ξ*
          (let ([F:wrap (F:Wrap C ctx (mk-α (-α:unvct ctx (Ξ:co-ctx Ξ₀))))]
                [F:mk (F:Ap (list (vec-len T^) {set 'make-vector}) '() ℓ)])
            (K+ F:mk (K+ F:wrap Ξ₀))))
        {set (⟦mon⟧ ⊥Ρ Φ^ Ξ* Σ)})))

  (: mon-Vect/C : Vect/C → ⟦C⟧)
  (define ((mon-Vect/C C) V ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (Vect/C αℓs) C)
    (define n (length αℓs))

    (define ((chk-elems [T^ : T^]) [Φ^ : Φ^])
      (define ⟦mon⟧s : (Listof EΡ)
        (for/list ([αℓᵢ (in-list αℓs)] [i (in-naturals)] #:when (index? i))
          (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
          (define ⟦elem⟧
            (mk-app (ℓ-with-id ℓ (list 'mon-vector/c i))
                    (mk-T 'vector-ref)
                    (list (mk-T T^) (mk-T (-b i)))))
          (EΡ (mk-mon (Ctx-with-ℓ ctx ℓᵢ) (mk-T (Σᵥ@ Σ αᵢ)) ⟦elem⟧) ⊥Ρ)))
      {set (match ⟦mon⟧s
             ['() (ret! (T->R (Vect '()) Φ^) Ξ₀ Σ)]
             [(cons (EΡ ⟦mon⟧ _) ⟦mon⟧s)
              (define F:wrap (F:Wrap C ctx (mk-α (-α:unvct ctx (Ξ:co-ctx Ξ₀)))))
              (define F:ap (F:Ap (list {set 'vector}) ⟦mon⟧s ℓ))
              (⟦mon⟧ ⊥Ρ Φ^ (K+ F:ap (K+ F:wrap Ξ₀)) Σ)])})

    (with-check Σ Φ^₀ ctx V 'vector?
      (λ (R^)
        (define-values (T^ Φ^) (collapse-R^-1 Σ R^))
        (define Vₗ (vec-len T^))
        (with-2-paths/collapse (λ () (split-results Σ (R (list Vₗ {set (-b n)}) Φ^) '=))
          (chk-elems T^)
          (λ _
            (define P (format-symbol "(vector-length/c ~a)" n))
            (blm (ℓ-with-src ℓ l+) lₒ (list P) (list V)))))))

  (: mon-Hash/C : Hash/C → ⟦C⟧)
  (define ((mon-Hash/C C) V ctx Φ^ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (Hash/C (αℓ αₖ ℓₖ) (αℓ αᵥ ℓᵥ)) C)
    (with-check Σ Φ^ ctx V 'hash?
      (λ (R^)
        (define αₕ (mk-α (-α:unhsh ctx (Ξ:co-ctx Ξ₀))))
        (for*/union : (℘ Ξ) ([Rᵢ (in-set R^)]
                             [Φ^ᵢ (in-value (R-_1 Rᵢ))]
                             [Vᵤ (in-set (T->V Σ Φ^ᵢ (car (R-_0 Rᵢ))))])
          (define (chk-key-vals [Vₖ : V^] [Vᵥ : V^])
            (define ⟦wrap⟧ (mk-wrapped C ctx αₕ {set Vᵤ}))
            (cond ;; FIXME hack for now
              [(or (set-empty? Vₖ) (set-empty? Vᵥ)) {set (⟦wrap⟧ ⊥Ρ Φ^ᵢ Ξ₀ Σ)}]
              [else
               (define ⟦mon⟧ (mk-mon (Ctx-with-ℓ ctx ℓᵥ) (mk-T (Σᵥ@ Σ αᵥ)) (mk-T Vᵥ)))
               (define Ξ* (K+ (F:Bgn (list ⟦mon⟧ ⟦wrap⟧) ⊥Ρ) Ξ₀))
               (mon (Σᵥ@ Σ αₖ) Vₖ ctx Φ^ᵢ Ξ* Σ)]))
          (match Vᵤ
            [(X/G _ (? Hash/C?) _)
             ;; TODO havoc would be expensive. Just wrap it for now
             (⊔T! Σ Φ^ᵢ αₕ Vᵤ)
             {set (ret! (T->R (X/G ctx C αₕ) Φ^ᵢ) Ξ₀ Σ)}]
            [(Hash^ α₁ α₂ _) (chk-key-vals (Σᵥ@ Σ α₁) (Σᵥ@ Σ α₂))]
            [_ (let ([●s {set (-● ∅)}]) (chk-key-vals ●s ●s))])))))

  (: mon-Set/C : Set/C → ⟦C⟧)
  (define ((mon-Set/C C) V ctx Φ^ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (Set/C (αℓ αₑ ℓₑ)) C)
    (with-check Σ Φ^ ctx V 'set?
      (λ (R^)
        (define αₛ (mk-α (-α:unset ctx (Ξ:co-ctx Ξ₀))))
        (for*/union : (℘ Ξ) ([Rᵢ (in-set R^)]
                             [Φ^ᵢ (in-value (R-_1 Rᵢ))]
                             [Vᵤ (in-set (T->V Σ Φ^ᵢ (car (R-_0 Rᵢ))))])
          (define (chk-elems [V^ : V^])
            (define ⟦wrap⟧ (mk-wrapped C ctx αₛ {set Vᵤ}))
            (cond
              [(set-empty? V^) {set (⟦wrap⟧ ⊥Ρ Φ^ᵢ Ξ₀ Σ)}]
              [else
               (define Ξ* (K+ (F:Bgn (list ⟦wrap⟧) ⊥Ρ) Ξ₀))
               (mon (Σᵥ@ Σ αₑ) V^ (Ctx-with-ℓ ctx ℓₑ) Φ^ᵢ Ξ* Σ)]))
          (match Vᵤ
            [(X/G _ (? Set/C?) _)
             ;; TODO havoc would be expensive. Just wrap for now
             (⊔T! Σ Φ^ᵢ αₛ Vᵤ)
             {set (ret! (T->R (X/G ctx C αₛ) Φ^ᵢ) Ξ₀ Σ)}]
            [(Set^ α _) (chk-elems (Σᵥ@ Σ α))]
            [_ (chk-elems {set (-● ∅)})])))))

  (: mon-Seal/C : Seal/C → ⟦C⟧)
  (define ((mon-Seal/C C) V ctx Φ^ Ξ₀ Σ)
    (match-define (Seal/C x H l) C)
    (match-define (Ctx l+ l- lo ℓ) ctx)
    (define α (mk-α (-α:sealed x H)))
    (cond
      [(equal? l l+) ; seal
       (⊔T! Σ Φ^ α V)
       {set (ret! (T->R (Sealed α) Φ^) Ξ₀ Σ)}]
      [(equal? l l-) ; unseal
       (define (er) (blm (ℓ-with-src ℓ l+) lo (list {set C}) (list V)))
       (define (ok) {set (ret! (T->R (Σᵥ@ Σ α) Φ^) Ξ₀ Σ)})
       (set-union-map
        (match-lambda
          [(Sealed (== α)) (ok)]
          [(-● _) {∪ (ok) (er)}]
          [_ (er)])
        (T->V Σ Φ^ V))]
      [else (error 'mon-seal/c "seal label ~a in context ~a, ~a, ~a" l l+ l- lo)]))

  (: mon-Flat/C : V → ⟦C⟧)
  (define ((mon-Flat/C C) V ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lo ℓ) ctx)
    (define (-blm [R^ : R^])
      (blm (ℓ-with-src ℓ l+) lo (list {set C}) (collapse-R^/W^ R^)))
    (with-3-paths (λ () (partition-results Σ (R (list V) Φ^₀) C))
      (λ ([R^ : R^]) {set (ret! R^ Ξ₀ Σ)})
      -blm
      (λ ([R^ : R^])
        (define-values (T^ Φ^) (collapse-R^-1 Σ R^))
        (define Ξ* (let ([T* (V^+ Σ T^ C)])
                     (K+ (F:If:Flat/C T* (-blm R^)) Ξ₀)))
        (match C
          [(? -b? b) ((app₁ 'equal?) (list T^ {set b}) ℓ Φ^ Ξ* Σ)]
          [_         ((app₁ C) (list T^) ℓ Φ^ Ξ* Σ)]))))

  (: Σᵥ@/ctx : Σ Ctx αℓ → (Values V^ Ctx))
  (define Σᵥ@/ctx
    (match-lambda**
     [(Σ ctx (αℓ α ℓ)) (values (Σᵥ@ Σ α) (Ctx-with-ℓ ctx ℓ))]))
  )
