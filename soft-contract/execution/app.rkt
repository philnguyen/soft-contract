#lang typed/racket/base

(provide app@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         syntax/parse/define
         set-extras
         bnf
         unreachable
         "../utils/patterns.rkt"
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(⟦F⟧ . ≜ . (Σ ℓ W → (Values R (℘ Err))))
(⟦G⟧ . ≜ . (Σ ℓ W V^ → (Values R (℘ Err))))

(define-unit app@
  (import meta-functions^ static-info^
          sto^ cache^ val^ pretty-print^
          prims^ prover^
          exec^ evl^ mon^ hv^ gc^)
  (export app^)

  (: app : Σ ℓ V^ W → (Values R (℘ Err)))
  (define (app Σ ℓ Vₕ^ W)
    (define W:root (W-root W))
    ((inst fold-ans V)
     (λ (Vₕ)
       (define root (∪ W:root (V-root Vₕ)))
       (define Σ* (gc root Σ))
       (ref-$! (intern-$:Key ($:Key:App Σ* ℓ Vₕ W))
               (λ () (with-gc root Σ* (λ () (app₁ Σ* ℓ Vₕ W))))))
     (unpack Vₕ^ Σ))) 

  (: app₁ : Σ ℓ V W → (Values R (℘ Err)))
  (define (app₁ Σ ℓ V W)
    (define f (match V
                [(? Clo? V) (app-Clo V)]
                [(? Case-Clo? V) (app-Case-Clo V)]
                [(-st-mk 𝒾) (app-st-mk 𝒾)]
                [(-st-p 𝒾) (app-st-p 𝒾)]
                [(-st-ac 𝒾 i) (app-st-ac 𝒾 i)]
                [(-st-mut 𝒾 i) (app-st-mut 𝒾 i)]
                [(? symbol? o) (app-prim o)]
                [(Guarded ctx (? Fn/C? G) α)
                 (cond [(==>i? G)    (app-==>i ctx G α)]
                       [(∀/C? G)     (app-∀/C  ctx G α)]
                       [(Case-=>? G) (app-Case-=> ctx G α)]
                       [else (app-Terminating/C ctx α)])]
                [(And/C α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-And/C α₁ α₂ ℓ)]
                [(Or/C  α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-Or/C  α₁ α₂ ℓ)]
                [(Not/C α ℓ) (app-Not/C α ℓ)]
                [(X/C α) (app-X/C α)]
                [(One-Of/C bs) (app-One-Of/C bs)]
                [(St/C 𝒾 αs ℓ) #:when (C-flat? V Σ) (app-St/C 𝒾 αs ℓ)]
                [(-● Ps) (app-opq Ps)]
                [(P:= T) (app-= T)]
                [V (app-err V)]))
    (f Σ ℓ W))

  (: app-Clo : Clo → ⟦F⟧)
  (define ((app-Clo Vₕ) Σ ℓ Wₓ*)
    (match-define (Clo fml E Ρ ℓₕ) Vₕ)
    (cond [(arity-includes? (shape fml) (length Wₓ*))
           (match-define (-var xs xᵣ) fml)
           (define Wₓ (unpack-W Wₓ* Σ))
           (define ΔΣₓ
             (let-values ([(W₀ Wᵣ) (if xᵣ (split-at Wₓ (length xs)) (values Wₓ '()))])
               (⧺ (stack-copy Ρ Σ)
                  (alloc-lex* xs W₀)
                  (if xᵣ (alloc-vararg xᵣ Wᵣ) ⊥ΔΣ))))
           ;; gc one more time against unpacked arguments
           ;; TODO: clean this up so only need to gc once?
           (let ([root (∪ (V-root Vₕ) (W-root Wₓ))])
             (define Σ* (gc root Σ))
             (define-values (rₐ es) (evl (⧺ Σ* ΔΣₓ) E)) ; no `ΔΣₓ` in result
             (define rn (trim-renamings (insert-fv-erasures ΔΣₓ (make-renamings fml Wₓ*))))
             (values (fix-return rn Σ* (ΔΣ⧺R ΔΣₓ rₐ)) es))]
          [else (err (Err:Arity ℓₕ (length Wₓ*) ℓ))]))

  (: app-Case-Clo : Case-Clo → ⟦F⟧)
  (define ((app-Case-Clo Vₕ) Σ ℓ Wₓ)
    (match-define (Case-Clo cases ℓₕ) Vₕ)
    (define n (length Wₓ))
    (match ((inst findf Clo) (λ (clo) (arity-includes? (shape (Clo-_0 clo)) n)) cases)
      [(? values clo) ((app-Clo clo) Σ ℓ Wₓ)]
      [#f (err (Err:Arity ℓₕ n ℓ))]))

  (: app-st-mk : -𝒾 → ⟦F⟧)
  (define ((app-st-mk 𝒾) Σ ℓ Wₓ)
    (define n (count-struct-fields 𝒾))
    (if (= n (length Wₓ))
        (let-values ([(αs ΔΣ) (alloc-each (unpack-W Wₓ Σ) (λ (i) (β:fld 𝒾 ℓ i)))])
          (just (St 𝒾 αs ∅) ΔΣ))
        (err (Err:Arity (-st-mk 𝒾) (length Wₓ) ℓ))))

  (: app-st-p : -𝒾 → ⟦F⟧)
  (define ((app-st-p 𝒾) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-p 𝒾) ℓ
      [(list _) (implement-predicate Σ (-st-p 𝒾) Wₓ)]))

  (: app-st-ac : -𝒾 Index → ⟦F⟧)
  (define ((app-st-ac 𝒾 i) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-ac 𝒾 i) ℓ
      [(list Vₓ)
       (with-split-Σ Σ (-st-p 𝒾) Wₓ
         (λ (Wₓ* ΔΣ₁) (with-pre ΔΣ₁ ((unchecked-app-st-ac 𝒾 i) (⧺ Σ ΔΣ₁) ℓ (car Wₓ*))))
         (λ (Wₓ* ΔΣ₂)
           (define ℓₒ (ℓ-with-src +ℓ₀ (-𝒾-name 𝒾)))
           (err (blm (ℓ-src ℓ) ℓ ℓₒ (list {set (-st-p 𝒾)}) Wₓ*))))]))

  (: unchecked-app-st-ac : -𝒾 Index → Σ ℓ V^ → (Values R (℘ Err)))
  (define ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)
    (define ac₁ : (V → (Values R (℘ Err)))
      (match-lambda
        [(St _ αs Ps)
         (define-values (V* ΔΣ)
           (refine (unpack (list-ref αs i) Σ) (ac-Ps (-st-ac 𝒾 i) Ps) Σ))
         (just V* ΔΣ)]
        [(and T (or (? T:@?) (? γ?))) #:when (not (struct-mutable? 𝒾 i))
         (define T* (T:@ (-st-ac 𝒾 i) (list T)))
         (if (set-empty? (unpack T* Σ)) (values ⊥R ∅) (just T*))]
        [(Guarded (cons l+ l-) (St/C _ αs ℓₕ) αᵥ)
         (with-collapsing/R [(ΔΣ Ws) ((unchecked-app-st-ac 𝒾 i) Σ ℓ (unpack αᵥ Σ))]
           (with-pre ΔΣ (mon (⧺ Σ ΔΣ) (Ctx l+ l- ℓₕ ℓ) (unpack (list-ref αs i) Σ) (car (collapse-W^ Ws)))))]
        [(and V₀ (-● Ps))
         (case (sat Σ (-st-p 𝒾) {set V₀})
           [(✗) (values ⊥R ∅)]
           [else
            (define V₁
              (if (prim-struct? 𝒾)
                  {set (-● ∅)}
                  ;; Track access to user-defined structs
                  (Σ@ (γ:escaped-field 𝒾 i) Σ)))
            (define-values (Vₐ ΔΣₐ) (refine V₁ (ac-Ps (-st-ac 𝒾 i) Ps) Σ))
            (just Vₐ ΔΣₐ)])]
        [(? α? α) (fold-ans ac₁ (unpack α Σ))]
        [_ (values ⊥R ∅)]))
    
    (fold-ans ac₁ Vₓ))

  (: app-st-mut : -𝒾 Index → ⟦F⟧)
  (define ((app-st-mut 𝒾 i) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-mut 𝒾 i) ℓ
      [(list Vₓ V*)
       (with-split-Σ Σ (-st-p 𝒾) (list Vₓ)
         (λ (Wₓ* ΔΣ₁) (with-pre ΔΣ₁ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ₁) ℓ (car Wₓ*) V*)))
         (λ (Wₓ* ΔΣ₂) (err (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set (-st-p 𝒾)}) Wₓ*))))]))

  (: unchecked-app-st-mut : -𝒾 Index → Σ ℓ V^ V^ → (Values R (℘ Err)))
  (define ((unchecked-app-st-mut 𝒾 i) Σ ℓ Vₓ V*)
    ((inst fold-ans V)
     (match-lambda
       [(St _ αs _) (just -void (mut (list-ref αs i) (blur V*)))]
       [(Guarded (cons l+ l-) (St/C _ αs ℓₕ) αᵥ)
        (with-collapsing/R [(ΔΣ Ws) (mon Σ (Ctx l- l+ ℓₕ ℓ) (unpack (list-ref αs i) Σ) V*)]
          (with-pre ΔΣ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ) ℓ (unpack αᵥ Σ) V*)))]
       [_ (just -void (alloc (γ:hv #f) V*))])
     Vₓ))

  (: app-prim : Symbol → ⟦F⟧)
  (define ((app-prim o) Σ ℓ Wₓ)
    ; TODO massage raw result
    ((get-prim o) Σ ℓ Wₓ))

  (: app-==>i : (Pairof -l -l) ==>i α → ⟦F⟧)
  (define ((app-==>i ctx:saved G αₕ) Σ₀-full ℓ Wₓ*)
    (match-define (cons l+ l-) ctx:saved)
    (define Wₓ (unpack-W Wₓ* Σ₀-full))
    (define Σ₀ (gc (∪ (set-add (V-root G) αₕ) (W-root Wₓ)) Σ₀-full))
    (match-define (==>i (-var Doms ?Doms:rest) Rngs) G)

    (: mon-doms : Σ -l -l (Listof Dom) W → (Values R (℘ Err)))
    (define (mon-doms Σ₀ l+ l- Doms₀ Wₓ₀)
      (let go ([Σ : Σ Σ₀] [Doms : (Listof Dom) Doms₀] [Wₓ : W Wₓ₀])
        (match* (Doms Wₓ)
          [('() '()) (values (R-of '()) ∅)]
          [((cons Dom Doms) (cons Vₓ Wₓ))
           (with-each-ans [(ΔΣₓ Wₓ*) (mon-dom Σ l+ l- Dom Vₓ)]
             (with-each-ans [(ΔΣ* W*) (go (⧺ Σ ΔΣₓ) Doms Wₓ)]
               (just (cons (car Wₓ*) W*) (⧺ ΔΣₓ ΔΣ*))))]
          [(_ _)
           (err (blm l+ ℓ #|FIXME|# (ℓ-with-src +ℓ₀ 'Λ) (map (compose1 (inst set V) Dom-ctc) Doms₀) Wₓ₀))])))

    (: mon-dom : Σ -l -l Dom V^ → (Values R (℘ Err)))
    (define (mon-dom Σ l+ l- dom V)
      (match-define (Dom x c ℓₓ) dom)
      (define ctx (Ctx l+ l- ℓₓ ℓ))
      (match c
        ;; Dependent domain
        [(Clo (-var xs #f) E Ρ _)
         (define ΔΣ₀ (stack-copy Ρ Σ))
         (define Σ₀ (⧺ Σ ΔΣ₀))
         (with-each-ans [(ΔΣ₁ W) (evl Σ₀ E)]
           (with-each-ans [(ΔΣ₂ W) (mon (⧺ Σ₀ ΔΣ₁) ctx (car W) V)]
             (match-define (list V*) W) ; FIXME catch
             (just W (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ (alloc (γ:lex x) V*)))))]
        ;; Non-dependent domain
        [(? α? α)
         (with-each-ans [(ΔΣ W) (mon Σ ctx (Σ@ α Σ₀) V)]
           (match-define (list V*) W)
           (just W (⧺ ΔΣ (alloc (γ:lex x) V*))))]))

    (define Dom-ref (match-lambda [(Dom x _ _) {set (γ:lex x)}]))

    (define (with-result [ΔΣ-acc : ΔΣ] [comp : (→ (Values R (℘ Err)))]) 
      (define-values (r es)
        (if Rngs
            (with-each-ans [(ΔΣₐ Wₐ) (comp)]
              (with-pre (⧺ ΔΣ-acc ΔΣₐ) (mon-doms (⧺ Σ₀ ΔΣ-acc ΔΣₐ) l+ l- Rngs Wₐ)))
            (with-pre ΔΣ-acc (comp))))
      (define rn (for/hash : (Immutable-HashTable α (Option α))
                     ([d (in-list Doms)]
                      [Vₓ (in-list Wₓ*)])
                   (values (γ:lex (Dom-name d))
                           (match Vₓ
                             [{singleton-set (? α? α)}
                              ;; renaming is only valid for values monitored by
                              ;; flat contract
                              #:when (and (α? (Dom-ctc d))
                                          (C^-flat? (unpack (Dom-ctc d) Σ₀) Σ₀))
                              α]
                             [_ #f]))))
      (values (fix-return rn Σ₀ r) es))

    (with-guarded-arity Wₓ G ℓ
      [Wₓ
       #:when (and (not ?Doms:rest) (= (length Wₓ) (length Doms)))
       (with-each-ans [(ΔΣₓ _) (mon-doms Σ₀ l- l+ Doms Wₓ)]
         (define args (map Dom-ref Doms))
         (with-result ΔΣₓ (λ () (app (⧺ Σ₀ ΔΣₓ) ℓ (Σ@ αₕ Σ₀) args))))]
      [Wₓ
       #:when (and ?Doms:rest (>= (length Wₓ) (length Doms)))
       (define-values (W₀ Wᵣ) (split-at Wₓ (length Doms)))
       (with-each-ans [(ΔΣ-init _) (mon-doms Σ₀ l- l+ Doms W₀)]
         (define-values (Vᵣ ΔΣᵣ) (alloc-rest (Dom-loc ?Doms:rest) Wᵣ))
         (with-each-ans [(ΔΣ-rest _) (mon-dom (⧺ Σ₀ ΔΣ-init ΔΣᵣ) l- l+ ?Doms:rest Vᵣ)]
           (define args-init (map Dom-ref Doms))
           (define arg-rest (Dom-ref ?Doms:rest))
           (with-result (⧺ ΔΣ-init ΔΣᵣ ΔΣ-rest)
             (λ () (app/rest (⧺ Σ₀ ΔΣ-init ΔΣᵣ ΔΣ-rest) ℓ (Σ@ αₕ Σ₀) args-init arg-rest)))))]))

  (: app-∀/C : (Pairof -l -l) ∀/C α → ⟦F⟧)
  (define ((app-∀/C ctx G α) Σ₀ ℓ Wₓ)
    (with-each-ans [(ΔΣ Wₕ) (inst-∀/C Σ₀ ctx G α ℓ)]
      (with-pre ΔΣ (app (⧺ Σ₀ ΔΣ) ℓ (car Wₕ) Wₓ))))

  (: app-Case-=> : (Pairof -l -l) Case-=> α → ⟦F⟧)
  (define ((app-Case-=> ctx G α) Σ ℓ Wₓ)
    (define n (length Wₓ))
    (match-define (Case-=> Cs) G)
    (match ((inst findf ==>i)
            (match-lambda [(==>i doms _) (arity-includes? (shape doms) n)])
            Cs)
      [(? values C) ((app-==>i ctx C α) Σ ℓ Wₓ)]
      [#f (err (Err:Arity G n ℓ))]))

  (: app-Terminating/C : Ctx α → ⟦F⟧)
  (define ((app-Terminating/C ctx α) Σ ℓ Wₓ)
    ???)

  (: app-And/C : α α ℓ → ⟦F⟧)
  (define ((app-And/C α₁ α₂ ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-ans [(ΔΣ₁ W₁) (app Σ ℓ (unpack α₁ Σ) Wₓ)]
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values W₁
           (λ (_ ΔΣ*) (with-pre (⧺ ΔΣ₁ ΔΣ*) (app (⧺ Σ₁ ΔΣ*) ℓ (unpack α₂ Σ) Wₓ)))
           (λ (_ ΔΣ*) (values (R-of -ff (⧺ ΔΣ₁ ΔΣ*)) ∅))))]))

  (: app-Or/C : α α ℓ → ⟦F⟧)
  (define ((app-Or/C α₁ α₂ ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-ans [(ΔΣ₁ W₁) (app Σ ℓ (unpack α₁ Σ) Wₓ)]
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values W₁
           (λ (_ ΔΣ*) (values (R-of W₁ (⧺ ΔΣ₁ ΔΣ*)) ∅))
           (λ (_ ΔΣ*) (with-pre (⧺ ΔΣ₁ ΔΣ*) (app (⧺ Σ₁ ΔΣ*) ℓ (unpack α₂ Σ) Wₓ)))))]))

  (: app-Not/C : α ℓ → ⟦F⟧)
  (define ((app-Not/C α ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-ans [(ΔΣ W) (app Σ ℓ (unpack α Σ) Wₓ)]
         (define Σ* (⧺ Σ ΔΣ))
         (with-split-Σ Σ* 'values W
           (λ (_ ΔΣ*) (just -ff (⧺ ΔΣ ΔΣ*)))
           (λ (_ ΔΣ*) (just -tt (⧺ ΔΣ ΔΣ*)))))]))

  (: app-X/C : α → ⟦F⟧)
  (define ((app-X/C α) Σ ℓ Wₓ) (app Σ ℓ (unpack α Σ) (unpack-W Wₓ Σ)))

  (: app-One-Of/C : (℘ Base) → ⟦F⟧)
  (define ((app-One-Of/C bs) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (One-Of/C bs) ℓ
      [(list V)
       (with-split-Σ Σ (One-Of/C bs) Wₓ
         (λ (_ ΔΣ) (just -tt ΔΣ))
         (λ (_ ΔΣ) (just -ff ΔΣ)))]))

  (: app-St/C : -𝒾 (Listof α) ℓ → ⟦F⟧)
  (define ((app-St/C 𝒾 αs ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list Vₓ)
       (with-split-Σ Σ (-st-p 𝒾) Wₓ
         (λ (Wₓ* ΔΣ*) (with-pre ΔΣ* ((app-St/C-fields 𝒾 0 αs ℓₕ) (⧺ Σ ΔΣ*) ℓ (car Wₓ*))))
         (λ (_ ΔΣ*) (just -ff ΔΣ*)))]))

  (: app-St/C-fields : -𝒾 Index (Listof α) ℓ → Σ ℓ V^ → (Values R (℘ Err)))
  (define ((app-St/C-fields 𝒾 i αs ℓₕ) Σ ℓ Vₓ)
    (match αs
      ['() (just -tt)]
      [(cons α αs)
       (with-collapsing/R [(ΔΣᵢ Wᵢs) ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)]
         (with-each-ans [(ΔΣₜ Wₜ) (app (⧺ Σ ΔΣᵢ) ℓ (unpack α Σ) (collapse-W^ Wᵢs))]
           (define ΔΣ (⧺ ΔΣᵢ ΔΣₜ))
           (define Σ* (⧺ Σ ΔΣ))
           (with-split-Σ Σ* 'values Wₜ
             (λ _ (with-pre ΔΣ ((app-St/C-fields 𝒾 (assert (+ 1 i) index?) αs ℓₕ) Σ* ℓ Vₓ)))
             (λ _ (just -ff ΔΣ)))))]))

  (: app-opq : (℘ P) → ⟦F⟧)
  (define ((app-opq Ps) Σ ℓ Wₓ*)
    (define Wₕ (list {set (-● Ps)}))
    (define ℓₒ (ℓ-with-src +ℓ₀ 'Λ))
    (with-split-Σ Σ 'procedure? Wₕ
      (λ _
        (define P-arity (P:arity-includes (length Wₓ*)))
        (with-split-Σ Σ P-arity Wₕ
          (λ _ (leak Σ (γ:hv #f) ((inst foldl V^ V^) ∪ ∅ (unpack-W Wₓ* Σ))))
          (λ _ (err (blm (ℓ-src ℓ) ℓ ℓₒ (list {set P-arity}) Wₕ)))))
      (λ _ (err (blm (ℓ-src ℓ) ℓ ℓₒ (list {set 'procedure?}) Wₕ)))))

  (: app-= : (U T -b) → ⟦F⟧)
  (define ((app-= T) Σ ℓ Wₓ) ((app-prim 'equal?) Σ ℓ (cons {set T} Wₓ)))

  (: app-err : V → ⟦F⟧)
  (define ((app-err V) Σ ℓ Wₓ)
    (err (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'procedure?}) (list {set V}))))

  (: app/rest : Σ ℓ V^ W V^ → (Values R (℘ Err)))
  (define (app/rest Σ ℓ Vₕ^ Wₓ Vᵣ)
    (define args:root (∪ (W-root Wₓ) (V^-root Vᵣ)))
    (define-values (Wᵣs snd?) (unalloc Vᵣ Σ))
    (define-values (r es) (fold-ans (λ ([Wᵣ : W]) (app Σ ℓ Vₕ^ (append Wₓ Wᵣ))) Wᵣs))
    (values r (if snd? es (set-add es (Err:Varargs Wₓ Vᵣ ℓ)))))

  (: trim-renamings : Renamings → Renamings)
  ;; Prevent some renaming from propagating based on what the caller has
  (define (trim-renamings rn)
    (for/fold ([rn : Renamings rn])
              ([(x ?T) (in-hash rn)]
               ;; FIXME this erasure is too aggressive
               #:when (T:@? ?T))
      (hash-set rn x #f)))

  (: insert-fv-erasures : ΔΣ Renamings → Renamings)
  ;; Add erasure of free variables that were stack-copied
  (define (insert-fv-erasures ΔΣ rn)
    (for/fold ([rn : Renamings rn]) ([α (in-hash-keys ΔΣ)]
                                     #:unless (hash-has-key? rn α))
      (hash-set rn α #f)))

  (: unalloc : V^ Σ → (Values (℘ W) Boolean))
  ;; Convert list in object language into one in meta-language
  (define (unalloc Vs Σ)
    (define-set touched : α #:mutable? #t)
    (define elems : (Mutable-HashTable Integer V^) (make-hasheq))
    (define-set ends : Integer #:eq? #t #:mutable? #t)
    (define sound? : Boolean #t)

    (let touch! ([i : Integer 0] [Vs : V^ Vs])
      (for ([V (in-set Vs)])
        (match V
          [(Cons αₕ αₜ)
           (hash-update! elems i (λ ([V₀ : V^]) (V⊔ V₀ (Σ@ αₕ Σ))) mk-∅)
           (cond [(touched-has? αₜ)
                  (set! sound? #f)
                  (ends-add! (+ 1 i))]
                 [else (touched-add! αₜ)
                       (touch! (+ 1 i) (Σ@ αₜ Σ))])]
          [(-b '()) (ends-add! i)]
          [_ (set! sound? #f)
             (ends-add! i)])))

    (define Ws (for/set: : W^ ([n (in-ends)])
                 (for/list : W ([i (in-range n)]) (hash-ref elems i))))
    (values Ws sound?))

  (: inst-∀/C : Σ (Pairof -l -l) ∀/C α ℓ → (Values R (℘ Err)))
  ;; Monitor function against freshly instantiated parametric contract
  (define (inst-∀/C Σ₀ ctx G α ℓ)
    (match-define (∀/C xs c Ρ ℓₒ) G)
    (match-define (cons l+ (and l- l-seal)) ctx)
    (define ΔΣ₀
      (let ([ΔΣ:seals
             (for/fold ([acc : ΔΣ ⊥ΔΣ]) ([x (in-list xs)])
               (define αₓ (α:dyn (β:sealed x ℓ) H₀))
               (⧺ acc
                  (alloc αₓ ∅)
                  (alloc (γ:lex x) {set (Seal/C αₓ l-seal)})))]
            [ΔΣ:stk (stack-copy Ρ Σ₀)])
        (⧺ ΔΣ:seals ΔΣ:stk)))
    (define Σ₁ (⧺ Σ₀ ΔΣ₀))
    (with-each-ans [(ΔΣ₁ W:c) (evl Σ₁ c)]
      (with-pre (⧺ ΔΣ₀ ΔΣ₁)
        (mon (⧺ Σ₁ ΔΣ₁) (Ctx l+ l- ℓₒ ℓ) (car W:c) (Σ@ α Σ₀)))))

  (define-simple-macro (with-guarded-arity W f ℓ [p body ...] ...)
    (match W
      [p body ...] ...
      [_ (err (Err:Arity f (length W) ℓ))]))
  
  )
