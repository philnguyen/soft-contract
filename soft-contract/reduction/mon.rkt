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
  (import static-info^
          val^ env^ evl^ sto^
          proof-system^
          reflection^ step^ app^ compile^ fc^)
  (export mon^)

  (⟦C⟧ . ≜ . (V^ Ctx Φ^ Ξ:co Σ → (℘ Ξ)))

  (: mon : V^ V^ Ctx Φ^ Ξ:co Σ → (℘ Ξ))
  (define (mon C^ V^ ctx Φ^ Ξ₀ Σ)
    (for/union : (℘ Ξ) ([C (in-set C^)]) ((mon₁ C) V^ ctx Φ^ Ξ₀ Σ)))

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
  (define ((mon-Fn/C C) V^₀ ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    
    (: blm : V → Any → (℘ Ξ))
    (define ((blm C) _)
      {set (Blm/simp (ℓ-with-src ℓ l+) lₒ (list {set C}) (list V^₀))})

    (: chk-arity : Φ^ → (℘ Ξ))
    (define (chk-arity Φ^)
      (define grd-arity {set (-b (guard-arity C))})
      (define val-arity
        (for/set : V^ ([Vᵢ (in-set V^₀)])
          (cond [(V-arity Vᵢ) => -b]
                [(S? Vᵢ) (S:@ 'procedure-arity (list Vᵢ))]
                [else (-● {set 'procedure-arity?})])))
      (with-2-paths
        (λ () (plausible-sats Σ Φ^ 'arity-includes? (list val-arity grd-arity)))
        wrap
        (blm (match (set-first grd-arity)
               [(-b (? integer? n))
                (format-symbol "(arity-includes/c ~a)" n)]
               [(-b (arity-at-least n))
                (format-symbol "(arity-at-leastc ~a)" n)]
               [(-b (list n ...))
                (string->symbol (format "(arity in ~a)" n))]))))

    (: wrap : Φ^ → (℘ Ξ))
    (define (wrap Φ^)
      (define α (mk-α (-α:fn ctx (Ξ:co-ctx Ξ₀))))
      (⊔ᵥ! Σ α V^₀)
      {set (ret! (V->R (X/G ctx C α) Φ^) Ξ₀ Σ)})
    
    (with-2-paths (λ () (plausible-sats Σ Φ^₀ 'procedure? (list V^₀)))
      (if (∀/C? C) wrap chk-arity)
      (blm 'procedure?)))

  (: mon-St/C : St/C → ⟦C⟧)
  (define ((mon-St/C C) V^₀ ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓ) ctx)
    (match-define (St/C _ 𝒾 αℓs) C)

    (: chk-fields : Φ^ → (℘ Ξ))
    (define (chk-fields Φ^)
      (define-values (αs ℓs) (unzip-by αℓ-_0 αℓ-_1 αℓs))
      (define all-immut? (struct-all-immutable? 𝒾))
      ???)

    (with-2-paths (λ () (plausible-sats Σ Φ^₀ (-st-p 𝒾) (list V^₀)))
      chk-fields
      (λ _ {set (Blm/simp (ℓ-with-src ℓ l+) lₒ (list (-st-p 𝒾)) (list V^₀))})))

  (: mon-X/C : X/C → ⟦C⟧)
  (define ((mon-X/C C) V ctx Φ^ Ξ Σ)
    (match-define (X/C α) C)
    (define C* (Σᵥ@ Σ α))
    {set (ret! (V->R V Φ^) (K+ (F:Mon:C ctx C*) Ξ) Σ)})

  (: mon-And/C : And/C → ⟦C⟧)
  (define ((mon-And/C C) V ctx Φ^ Ξ Σ)
    (match-define (And/C _ αℓ₁ αℓ₂) C)
    (define-values (C₁ ctx₁) (Σᵥ@/ctx Σ ctx αℓ₁))
    (define-values (C₂ ctx₂) (Σᵥ@/ctx Σ ctx αℓ₂))
    (define Ξ* (K+ (F:Mon:C ctx₁ C₁) (K+ (F:Mon:C ctx₂ C₂) Ξ)))
    {set (ret! (V->R V Φ^) Ξ* Σ)})

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
  (define (mon-One-Of/C C)
    (match-define (One-Of/C bs) C)
    ???)

  (: mon-Vectof : Vectof → ⟦C⟧)
  (define ((mon-Vectof C) V ctx Φ^₀ Ξ₀ Σ)
    (match-define (Ctx l+ _ lₒ ℓₘ) ctx)
    (match-define (Vectof αℓs) C)

    (: blm : P → Φ^ → (℘ Ξ))
    (define ((blm P) _)
      {set (Blm/simp (ℓ-with-src ℓₘ l+) lₒ (list P) (list V))})

    (: chk-elems : Φ^ → (℘ Ξ))
    (define (chk-elems Φ^)
      ???)
    
    (with-2-paths (λ () (plausible-sats Σ Φ^₀ 'vector? (list V)))
      chk-elems
      (blm 'vector?)))

  (: mon-Vect/C : Vect/C → ⟦C⟧)
  (define (mon-Vect/C C) ???)

  (: mon-Hash/C : Hash/C → ⟦C⟧)
  (define (mon-Hash/C C) ???)

  (: mon-Set/C : Set/C → ⟦C⟧)
  (define (mon-Set/C C) ???)

  (: mon-Seal/C : Seal/C → ⟦C⟧)
  (define ((mon-Seal/C C) V ctx Φ^ Ξ₀ Σ)
    (match-define (Seal/C x H l) C)
    (match-define (Ctx l+ l- lo ℓ) ctx)
    (define α (mk-α (-α:sealed x H)))
    (cond
      [(equal? l l+) ; seal
       (⊔ᵥ! Σ α V)
       {set (ret! (V->R (Sealed α) Φ^) Ξ₀ Σ)}]
      [(equal? l l-) ; unseal
       (define (er) {set (Blm/simp (ℓ-with-src ℓ l+) lo (list {set C}) (list V))})
       (define (ok) {set (ret! (V->R (Σᵥ@ Σ α) Φ^) Ξ₀ Σ)})
       (for/union : (℘ Ξ) ([Vᵢ (in-set V)])
         (match Vᵢ
           [(Sealed (== α)) (ok)]
           [(-● _) {∪ (ok) (er)}]
           [_ (er)]))]
      [else (error 'mon-seal/c "seal label ~a in context ~a, ~a, ~a" l l+ l- lo)]))

  (: mon-Flat/C : V → ⟦C⟧)
  (define ((mon-Flat/C C) V ctx Φ^₀ Ξ Σ)
    (match-define (Ctx l+ _ lo ℓ) ctx)
    (with-3-paths (λ () (partition-sats Σ Φ^₀ C V))
      (λ ([Φ^ : Φ^]) {set (ret! (V->R V Φ^) Ξ Σ)})
      (λ _ {set (Blm/simp (ℓ-with-src ℓ l+) lo (list {set C}) (list V))})
      (λ ([Φ^ : Φ^])
        ???)))

  #|

  (: mon-struct/c : -ctx -St/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-struct/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓₘ) ctx)
    (match-define (-St/C flat? 𝒾 αℓs) C)
    (define σ (-Σ-σ Σ))
    (define p (-st-p 𝒾))

    (: chk-fields : -φ → (℘ -ς))
    (define (chk-fields φ)
      (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
      (define all-immutable? (struct-all-immutable? 𝒾))
      (define ⟦field⟧s : (Listof -⟦e⟧)
        (let ([V^* (V+ σ φ V^ p)])
          (for/list ([α (in-list αs)]
                     [i (in-naturals)] #:when (index? i))
            (mk-app (ℓ-with-id ℓₘ (list 'mon-struct/c 𝒾 i)) (mk-V (-st-ac 𝒾 i)) (list (mk-A (list V^*)))))))
      (define ⟦mon⟧s : (Listof -⟦e⟧)
        (for/list ([Cᵢ (σ@/list Σ (-φ-cache φ) αs)] [⟦field⟧ᵢ ⟦field⟧s] [ℓᵢ : ℓ ℓs])
          (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-A (list Cᵢ)) ⟦field⟧ᵢ)))
      (define ⟦reconstr⟧ (mk-app ℓₘ (mk-V (-st-mk 𝒾)) ⟦mon⟧s))
      (define ⟦k⟧* (if all-immutable? ⟦k⟧ (wrap-st∷ C ctx ⟦k⟧)))
      (⟦reconstr⟧ ⊥ρ H φ Σ ⟦k⟧*))

    (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ p V^)]) : -ς
      #:true (chk-fields φ₁)
      #:false (let ([blm (blm/simp l+ lo (list p) (list V^) ℓₘ)])
                (⟦k⟧ blm H φ₂ Σ))))

  (: mon-one-of/c : -ctx -One-Of/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-one-of/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-One-Of/C bs) C)
    (define (blm) (⟦k⟧ (blm/simp l+ lo (list {set C}) (list V^) ℓ) H φ Σ))
    (case (sat-one-of V^ bs)
      [(✓) (⟦k⟧ (list V^) H φ Σ)]
      [(✗) (blm)]
      [(?) (∪ (⟦k⟧ (list (list->set (set-map bs -b))) H φ Σ) (blm))]))

  (: mon-vectorof : -ctx -V -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-vectorof ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Vectorof (-⟪α⟫ℓ α* ℓ*)) C)
    (define σ (-Σ-σ Σ))

    (: blm : -h -φ → (℘ -ς))
    (define (blm C φ)
      (define blm (blm/simp l+ lo (list C) (list V^) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: chk-elems : -φ → (℘ -ς))
    (define (chk-elems φ)
      (define V^* (V+ σ φ V^ C))
      (define ⟦ref⟧
        (mk-app (ℓ-with-id ℓ (list 'mon-vectorof))
                (mk-V 'vector-ref)
                (list (mk-A (list V^*)) (mk-V (-● {set 'exact-nonnegative-integer?})))))
      (define ⟦k⟧* (mk-wrap-vect∷ C ctx ⟦k⟧))
      (define Vₗ^ (r:vec-len σ φ V^*))
      (define C*^ (σ@ Σ (-φ-cache φ) α*))
      (define ⟦mon⟧ (mk-mon (ctx-with-ℓ ctx ℓ*) (mk-A (list C*^)) ⟦ref⟧))
      (⟦mon⟧ ⊥ρ H φ Σ (ap∷ (list Vₗ^ {set 'make-vector}) '() ⊥ρ ℓ ⟦k⟧*)))

    (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'vector? V^)]) : -ς
      #:true  (chk-elems φ₁)
      #:false (blm 'vector? φ₂)))

  (: mon-vector/c : -ctx -Vector/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-vector/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Vector/C ⟪α⟫ℓs) C)
    (define σ (-Σ-σ Σ))
    (define n (length ⟪α⟫ℓs))
    
    (: blm : -h -φ → (℘ -ς))
    (define (blm C φ)
      (define blm (blm/simp l+ lo (list C) (list V^) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: chk-len : -φ → (℘ -ς))
    (define (chk-len φ)
      (define Vₙ^ (r:vec-len σ φ V^))
      (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ '= Vₙ^ {set (-b n)})]) : -ς
        #:true  (chk-flds φ₁)
        #:false (blm (format-symbol "vector-length/c ~a" n) φ₂)))

    (: chk-flds : -φ → (℘ -ς))
    (define (chk-flds φ)
      (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc ⟪α⟫ℓs))
      (define V^* (V+ σ φ V^ C))
      (define Cs (σ@/list σ (-φ-cache φ) αs))
      (define ⟦mon-fld⟧s : (Listof -⟦e⟧)
        (for/list ([Cᵢ (in-list Cs)] [ℓᵢ (in-list ℓs)] [i (in-naturals)] #:when (index? i))
          (define ⟦ref⟧
            (mk-app (ℓ-with-id ℓ (list 'mon-vector/c i))
                    (mk-V 'vector-ref)
                    (list (mk-A (list V^*)) (mk-V (-b i)))))
          (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-A (list Cᵢ)) ⟦ref⟧)))
      
      (match ⟦mon-fld⟧s
        ['() (⟦k⟧ (list {set (-Vector '())}) H φ Σ)] ; no need to wrap
        [(cons ⟦fld⟧₀ ⟦fld⟧s)
         (define ⟦k⟧* (mk-wrap-vect∷ C ctx ⟦k⟧))
         (⟦fld⟧₀ ⊥ρ H φ Σ
                 (ap∷ (list {set 'vector}) ⟦fld⟧s ⊥ρ ℓ ⟦k⟧*))]))

    (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'vector? V^)]) : -ς
      #:true  (chk-len φ₁)
      #:false (blm 'vector? φ₂)))

  (: mon-hash/c : -ctx -Hash/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-hash/c ctx C Vᵤ^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Hash/C (-⟪α⟫ℓ αₖ ℓₖ) (-⟪α⟫ℓ αᵥ ℓᵥ)) C)
    (define σ (-Σ-σ Σ))

    (: chk-content : -φ → (℘ -ς))
    (define (chk-content φ)
      (define αₕ (-α->⟪α⟫ (-α.unhsh ctx H)))
      
      (: chk-key-vals : -V^ -V^ → (℘ -ς))
      (define (chk-key-vals Vₖ^ Vᵥ^)
        (define wrap (mk-wrapped-hash C ctx αₕ (V+ σ φ Vᵤ^ 'hash?)))
        (cond ;; FIXME hacks for now
          [(or (set-empty? Vₖ^) (set-empty? Vᵥ^))
           (wrap ⊥ρ H φ Σ ⟦k⟧)]
          [else
           (define doms (σ@ Σ (-φ-cache φ) αₖ))
           (define rngs (σ@ Σ (-φ-cache φ) αᵥ))
           (define mon-vals (mk-mon (ctx-with-ℓ ctx ℓᵥ) (mk-A (list rngs)) (mk-A (list Vᵥ^))))
           (define ⟦k⟧* (bgn∷ (list mon-vals wrap) ⊥ρ ⟦k⟧))
           (push-mon (ctx-with-ℓ ctx ℓₖ) doms Vₖ^ H φ Σ ⟦k⟧*)]))

      (for/union : (℘ -ς) ([Vᵤ (in-set Vᵤ^)])
        (match Vᵤ^
          [(? -Hash/guard?)
           ;; havoc would be expensive. Just wrap it for now
           (define φ* (alloc Σ φ αₕ Vᵤ^))
           (⟦k⟧ (list {set (-Hash/guard C αₕ ctx)}) H φ* Σ)]
          [(-Hash^ α₁ α₂ _)
           (chk-key-vals (σ@ Σ (-φ-cache φ) α₁) (σ@ Σ (-φ-cache φ) α₂))]
          [_
           (define ●s {set (-● ∅)})
           (chk-key-vals ●s ●s)])))

    (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'hash? Vᵤ^)]) : -ς
      #:true (chk-content φ₁)
      #:false (let ([blm (blm/simp l+ lo '(hash?) (list Vᵤ^) ℓ)])
                (⟦k⟧ blm H φ₂ Σ))))

  (: mon-set/c : -ctx -Set/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-set/c ctx C Vᵤ^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Set/C (-⟪α⟫ℓ αₑ ℓₑ)) C)
    (define σ (-Σ-σ Σ))

    (: chk-content : -φ → (℘ -ς))
    (define (chk-content φ)
      (define αₛ (-α->⟪α⟫ (-α.unset ctx H)))

      (: chk-elems : -V^ → (℘ -ς))
      (define (chk-elems Vs)
        (define wrap (mk-wrapped-set C ctx αₛ (V+ σ φ Vᵤ^ 'set?)))
        (cond
          [(set-empty? Vs)
           (wrap ⊥ρ H φ Σ ⟦k⟧)]
          [else
           (define ⟦k⟧* (bgn∷ (list wrap) ⊥ρ ⟦k⟧))
           (push-mon (ctx-with-ℓ ctx ℓₑ) (σ@ σ (-φ-cache φ) αₑ) Vs H φ Σ ⟦k⟧*)]))

      (for/union : (℘ -ς) ([Vᵤ (in-set Vᵤ^)])
        (match Vᵤ
          [(? -Set/guard?)
           (define φ* (alloc Σ φ αₛ {set Vᵤ}))
           (⟦k⟧ (list {set (-Set/guard C αₛ ctx)}) H φ* Σ)]
          [(-Set^ α _) (chk-elems (σ@ σ (-φ-cache φ) α))]
          [_ (chk-elems {set (-● ∅)})])))

    (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'set? Vᵤ^)]) : -ς
      #:true (chk-content φ₁)
      #:false (let ([blm (blm/simp l+ lo '(set?) (list Vᵤ^) ℓ)])
                (⟦k⟧ blm H φ₂ Σ))))

  (: mon-flat/c : -ctx -V -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-flat/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (define (blm) (blm/simp l+ lo (list {set C}) (list V^) ℓ))
    (case (V∈C (-Σ-σ Σ) φ V^ C)
      [(✓) (⟦k⟧ (list V^) H φ Σ)]
      [(✗) (⟦k⟧ (blm) H φ Σ)]
      [(?)
       (define V^* (V+ (-Σ-σ Σ) φ V^ C))
       (define ⟦k⟧* (if.flat/c∷ V^* (blm) ⟦k⟧))
       (match C
         [(? -b? b) (app ℓ {set 'equal?} (list V^ {set b}) H φ Σ ⟦k⟧*)]
         [_         (app ℓ {set C      } (list V^        ) H φ Σ ⟦k⟧*)])]))

|#
  )
