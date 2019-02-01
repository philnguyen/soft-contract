#lang typed/racket/base

(provide mon@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         bnf
         set-extras
         unreachable
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

  (: mon : Σ Ctx V^ V^ → (Values R (℘ Err)))
  (define (mon Σ ctx C^ V^)
    (define args:root (V^-root V^))
    (fold-ans (λ ([C : V]) ((mon₁ C) (gc (∪ (V-root C) args:root) Σ) ctx V^)) C^))

  (: mon* : Σ Ctx W W → (Values R (℘ Err)))
  (define (mon* Σ₀ ctx Cs Vs)
    (if (= (length Cs) (length Vs))
        (let loop ([ΔΣ : ΔΣ ⊥ΔΣ] [Σ : Σ Σ₀] [rev-As : W '()] [es : (℘ Err) ∅] [Cs : W Cs] [Vs : W Vs])
          (match* (Cs Vs)
            [((cons C₁ Cs*) (cons V₁ Vs*))
             (define-values (r₁ es₁) (mon Σ ctx C₁ V₁))
             (match (collapse-R r₁)
               [(cons (app collapse-W^ (app car A₁)) ΔΣ₁)
                (loop (⧺ ΔΣ ΔΣ₁) (⧺ Σ ΔΣ₁) (cons A₁ rev-As) (∪ es es₁) Cs* Vs*)]
               [#f (values ⊥R (∪ es es₁))])]
            [('() '())
             (values (R-of (reverse rev-As) ΔΣ) es)]))
        (match-let ([(Ctx l+ _ ℓₒ ℓ) ctx])
          (err (Blm l+ ℓ ℓₒ Cs Vs)))))

  (: mon₁ : V → Σ Ctx V^ → (Values R (℘ Err)))
  (define (mon₁ C) 
    (define f
      (cond [(Fn/C? C) (mon-Fn/C C)]
            [(St/C? C) (mon-St/C C)]
            [(α? C) (mon-α C)]
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
    (λ (Σ ctx V)
      (ref-$! ($:Key:Mon Σ ctx C V) (λ () (f Σ ctx V)))))

  (: mon-Fn/C : Fn/C → ⟦C⟧)
  (define ((mon-Fn/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (define C:arity (guard-arity C))
    (define (blm [V : V]) (Blm l+ ℓₒ ℓ (list {set C}) (list {set V})))
    (define (wrap [Vₕ : V])
      (define αᵥ (α:dyn (β:fn ctx) H₀))
      (just (Guarded ctx C αᵥ) (alloc αᵥ {set Vₕ})))
    ((inst fold-ans V)
     (match-lambda
       [(and V (or (? Clo?) (? Case-Clo?) (Guarded _ (? Fn/C?) _) (? -o?)))
        #:when (arity-includes? (assert (arity V)) C:arity)
        (wrap V)]
       [(and V (-● Ps))
        (if (∋ Ps 'procedure?) (wrap (-● Ps)) (err (blm V)))]
       [V (err (blm V))])
     Vs))

  (: mon-St/C : St/C → ⟦C⟧)
  (define ((mon-St/C C) Σ₀ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (match-define (St/C 𝒾 αs ℓₕ) C)

    (: mon-St/C-fields : Σ V^ → (Values R (℘ Err)))
    (define (mon-St/C-fields Σ V)
      (let go ([i : Index 0] [αs : (Listof α) αs] [Vs-rev : W '()] [ΔΣ : ΔΣ ⊥ΔΣ])
        (match αs
          ['() (just (reverse Vs-rev) ΔΣ)]
          [(cons αᵢ αs*)
           (with-collapsing/R [(ΔΣ₀ Ws) (app (⧺ Σ ΔΣ) ℓ {set (-st-ac 𝒾 i)} (list Vs))]
             (with-collapsing/R [(ΔΣ₁ Ws*) (mon (⧺ Σ ΔΣ ΔΣ₀) ctx (unpack αᵢ Σ) (car (collapse-W^ Ws)))]
               (go (assert (+ 1 i) index?)
                   αs*
                   (cons (car (collapse-W^ Ws*)) Vs-rev)
                   (⧺ ΔΣ ΔΣ₀ ΔΣ₁))))])))
    
    (with-split-Σ Σ₀ (-st-p 𝒾) (list Vs)
      (λ (W* ΔΣ)
        (with-collapsing/R [(ΔΣ* Ws) (mon-St/C-fields (⧺ Σ₀ ΔΣ) (car W*))]
          (define-values (αs ΔΣ**) (alloc-each (collapse-W^ Ws) (λ (i) (β:fld 𝒾 ℓₕ i))))
          (define V* {set (St 𝒾 αs)})
          (if (struct-all-immutable? 𝒾)
              (just V* (⧺ ΔΣ ΔΣ* ΔΣ**))
              (let ([α (α:dyn (β:st 𝒾 ctx) H₀)])
                (just (Guarded ctx C α) (⧺ ΔΣ ΔΣ* ΔΣ** (alloc α V*)))))))
      (λ (W* ΔΣ) (err (Blm l+ ℓ ℓₒ (list {set C}) W*))))) 

  (: mon-α : α → ⟦C⟧)
  (define ((mon-α α) Σ ctx V^) (mon Σ ctx (unpack α Σ) V^))

  (: mon-And/C : And/C → ⟦C⟧)
  (define ((mon-And/C C) Σ ctx V^)
    (match-define (And/C α₁ α₂ ℓ) C)
    (define-values (r₁ es₁) ((mon₁ α₁) Σ ctx V^))
    (match (collapse-R r₁)
      [(cons (app collapse-W^ (app car V₁)) ΔΣ₁)
       (define-values (r₂ es₂) ((mon₁ α₂) (⧺ Σ ΔΣ₁) ctx V₁))
       (values (ΔΣ⧺R ΔΣ₁ r₂) (∪ es₁ es₂))]
      [#f (values ⊥R es₁)]))

  (: mon-Or/C : Or/C → ⟦C⟧)
  (define ((mon-Or/C C) Σ ctx V)
    (match-define (Or/C α₁ α₂ _) C)

    (: chk : V^ V^ → (Values R (℘ Err)))
    (define (chk C-fo C-ho)
      (with-each-path [(ΔΣ Ws) (app Σ (Ctx-origin ctx) C-fo (list V))]
        (with-split-Σ (⧺ Σ ΔΣ) 'values (collapse-W^ Ws)
          (λ (_ ΔΣ*) (let-values ([(V* ΔΣ**) (refine V α₁ Σ)])
                       (just V* (⧺ ΔΣ ΔΣ* ΔΣ**))))
          (λ (_ ΔΣ*) (mon (⧺ Σ ΔΣ ΔΣ*) ctx C-ho V)))))

    (let ([C₁ (unpack α₁ Σ)]
          [C₂ (unpack α₂ Σ)])
      (cond [(C^-flat? C₁ Σ) (chk C₁ C₂)]
            [(C^-flat? C₂ Σ) (chk C₂ C₁)]
            [else (error 'or/c "No more than 1 higher-order disjunct for now")])))

  (: mon-Not/C : Not/C → ⟦C⟧)
  (define ((mon-Not/C C) Σ ctx V)
    (match-define (Not/C α _) C)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-each-path [(ΔΣ Ws) (app Σ ℓₒ (unpack α Σ) (list V))]
      (with-split-Σ (⧺ Σ ΔΣ) 'values (collapse-W^ Ws)
        (λ _ (err (Blm (ℓ-src ℓ) ℓ ℓₒ (list {set C}) (list V))))
        (λ (_ ΔΣ*) (let-values ([(V* ΔΣ**) (refine V C Σ)])
                     (just V* (⧺ ΔΣ ΔΣ* ΔΣ**)))))))

  (: mon-One-Of/C : One-Of/C → ⟦C⟧)
  (define ((mon-One-Of/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-split-Σ Σ C (list Vs)
      (λ (W ΔΣ) (just W ΔΣ))
      (λ (W ΔΣ) (err (Blm l+ ℓ ℓₒ (list {set C}) W)))))

  (: mon-Vectof/C : Vectof/C → ⟦C⟧)
  (define ((mon-Vectof/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (with-split-Σ Σ 'vector? (list Vs)
      (λ (W* ΔΣ₀)
        (match-define (Vectof/C αₕ _) C)
        (define N (-● {set 'exact-nonnegative-integer?}))
        (define Σ₀ (⧺ Σ ΔΣ₀))
        (with-collapsing/R [(ΔΣ₁ Wₑs) (app Σ₀ ℓ {set 'vector-ref} (list (car W*) {set N}))]
          (with-collapsing/R [(ΔΣ₂ Wₑs*) (mon (⧺ Σ₀ ΔΣ₁) ctx (unpack αₕ Σ) (car (collapse-W^ Wₑs)))]
            (define Vₑ (car (collapse-W^ Wₑs*)))
            (define αₑ (α:dyn (β:vct ℓ) H₀))
            (define αᵥ (α:dyn (β:unvct ctx) H₀))
            (just (Guarded ctx C αᵥ)
                  (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ (alloc αₑ Vₑ) (alloc αᵥ {set (Vect-Of αₑ {set N})}))))))
      (λ (W* _) (err (Blm l+ ℓₒ ℓ (list {set C}) W*)))))

  (: mon-Vect/C : Vect/C → ⟦C⟧)
  (define ((mon-Vect/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (match-define (Vect/C αs _) C)
    (define n (length αs))
    (define (@ [α : α]) (unpack α Σ))

    (define (blm [V : V]) (Blm l+ ℓₒ ℓ (list {set C}) (list {set V})))

    (: check-elems+wrap : W → (Values R (℘ Err)))
    (define (check-elems+wrap W)
      (with-collapsing/R [(ΔΣ Ws) (mon* Σ ctx (map @ αs) W)]
        (define W* (collapse-W^ Ws))
        (define αᵥ (α:dyn (β:unvct ctx) H₀))
        (define-values (αs* ΔΣ*) (alloc-each W* (λ (i) (β:idx ℓ i))))
        (just (Guarded ctx C αᵥ) (⧺ ΔΣ ΔΣ* (alloc αᵥ {set (Vect αs*)})))))
    
    ((inst fold-ans V)
     (match-lambda
       [(Vect αs*)
        #:when (= (length αs*) n)
        (check-elems+wrap (map @ αs*))]
       [(Vect-Of αᵥ Vₙ)
        (check-elems+wrap (make-list n (@ αᵥ)))]
       [(and V (? Guarded?))
        (define-values (args-rev ΔΣ₀ es₀)
          (for/fold ([args-rev : W '()] [ΔΣ : (Option ΔΣ) ⊥ΔΣ] [es : (℘ Err) ∅])
                    ([i (in-range n)] #:when ΔΣ)
            (define-values (rᵢ esᵢ) (app Σ ℓₒ {set 'vector-ref} (list {set V} {set (-b i)})))
            (match (collapse-R rᵢ)
              [(cons Wsᵢ ΔΣᵢ) (values (cons (car (collapse-W^ Wsᵢ)) args-rev)
                                      (⧺ (assert ΔΣ) ΔΣᵢ)
                                      (∪ es esᵢ))]
              [#f (values '() #f (∪ es esᵢ))])))
        (if ΔΣ₀
            (let-values ([(r* es*) (check-elems+wrap (reverse args-rev))])
              (values (ΔΣ⧺R ΔΣ₀ r*) (∪ es₀ es*)))
            (values ⊥R es₀))]
       [(and V (-● Ps))
        (if (∋ Ps 'vector?)
            (check-elems+wrap (make-list n {set (-● ∅)}))
            (err (blm V)))]
       [V (err (blm V))])
     Vs))

  (: mon-Hash/C : Hash/C → ⟦C⟧)
  (define ((mon-Hash/C C) Σ ctx V^)
    ???)

  (: mon-Set/C : Set/C → ⟦C⟧)
  (define ((mon-Set/C C) Σ ctx V^)
    ???)

  (: mon-Seal/C : Seal/C → ⟦C⟧)
  (define ((mon-Seal/C C) Σ ctx V^)
    ???)

  (: mon-Flat/C : V → ⟦C⟧)
  (define ((mon-Flat/C C) Σ ctx Vs)
    (match-define (Ctx l+ _ ℓₒ ℓ) ctx)
    (define (blm) (Blm l+ ℓ ℓₒ (list {set C}) (list Vs)))
    (case (sat Σ C Vs)
      [(✓) (just Vs)]
      [(✗) (err (blm))]
      [else
       (with-each-path [(ΔΣ Ws) (app Σ ℓₒ {set C} (list Vs))]
         (with-split-Σ (⧺ Σ ΔΣ) 'values (collapse-W^ Ws)
           (λ (_ ΔΣ₁) (let-values ([(V* ΔΣ*) (refine Vs C Σ)])
                        (just V* (⧺ ΔΣ ΔΣ₁ ΔΣ*))))
           (λ _ (err (blm)))))]))

  )
