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
       (ref-$! ($:Key:App Σ* ℓ Vₕ W)
               (λ () (with-gc root (λ () (app₁ Σ* ℓ Vₕ W))))))
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
             (values (adjust-return Σ ΔΣₓ fml Wₓ* rₐ) es))]
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
        (let-values ([(αs ΔΣ) (alloc-each Wₓ (λ (i) (β:fld 𝒾 ℓ i)))])
          (just (St 𝒾 αs) ΔΣ))
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
           (err (Blm (ℓ-src ℓ) ℓ ℓₒ (list {set (-st-p 𝒾)}) Wₓ*))))]))

  (: unchecked-app-st-ac : -𝒾 Index → Σ ℓ V^ → (Values R (℘ Err)))
  (define ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)
    ((inst fold-ans V)
     (match-lambda
       [(St _ αs) (just (unpack (list-ref αs i) Σ))]
       [(and T (or (? T:@?) (? γ?))) (just (T:@ (-st-ac 𝒾 i) (list T)))]
       [(Guarded ctx (St/C _ αs ℓₕ) αᵥ)
        (with-collapsing/R [(ΔΣ Ws) ((unchecked-app-st-ac 𝒾 i) Σ ℓ (unpack αᵥ Σ))]
          (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (unpack (list-ref αs i) Σ) (car (collapse-W^ Ws)))))]
       [(and V (-● Ps))
        (case (sat Σ (-st-p 𝒾) {set V})
          [(✗) (values ⊥R ∅)]
          [else
           (just (cond
                   ;; Special case for rest of `list?`. TODO: reduce hack
                   [(and (equal? 𝒾 -𝒾-cons) (equal? i 1) (∋ Ps 'list?))
                    (-● {set 'list?})]
                   ;; Track access to user-defined structs
                   [(not (member 𝒾 (list -𝒾-cons -𝒾-box)))
                    (unpack (γ:escaped-field 𝒾 i) Σ)]
                   [else (-● ∅)]))])]
       [_ (values ⊥R ∅)])
     Vₓ))

  (: app-st-mut : -𝒾 Index → ⟦F⟧)
  (define ((app-st-mut 𝒾 i) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-mut 𝒾 i) ℓ
      [(list Vₓ V*)
       (with-split-Σ Σ (-st-p 𝒾) (list Vₓ)
         (λ (Wₓ* ΔΣ₁) (with-pre ΔΣ₁ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ₁) ℓ (car Wₓ*) V*)))
         (λ (Wₓ* ΔΣ₂) (err (Blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set (-st-p 𝒾)}) Wₓ*))))]))

  (: unchecked-app-st-mut : -𝒾 Index → Σ ℓ V^ V^ → (Values R (℘ Err)))
  (define ((unchecked-app-st-mut 𝒾 i) Σ ℓ Vₓ V*)
    ((inst fold-ans V)
     (match-lambda
       [(St _ αs) (just -void (mut (list-ref αs i) V*))]
       [(Guarded ctx (St/C _ αs ℓₕ) αᵥ)
        (with-collapsing/R [(ΔΣ Ws) (mon Σ (Ctx-flip ctx) (unpack (list-ref αs i) Σ) V*)]
          (with-pre ΔΣ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ) ℓ (unpack αᵥ Σ) V*)))]
       [_ (just -void (alloc (γ:hv #f) V*))])
     Vₓ))

  (: app-prim : Symbol → ⟦F⟧)
  (define ((app-prim o) Σ ℓ Wₓ)
    ; TODO massage raw result
    ((get-prim o) Σ ℓ Wₓ))

  (: app-==>i : Ctx ==>i α → ⟦F⟧)
  (define ((app-==>i ctx G αₕ) Σ₀ ℓ Wₓ)
    (match-define (==>i (-var Doms ?Doms:rest) Rngs) G)
    (define (@ [α : α]) (lookup α Σ₀))

    (: mon-doms : Σ Ctx (Listof Dom) W → (Values R (℘ Err)))
    (define (mon-doms Σ₀ ctx Doms₀ Wₓ₀)
      (match-define (Ctx l+ l- ℓₒ ℓₘ) ctx)
      (let go ([Σ : Σ Σ₀] [Doms : (Listof Dom) Doms₀] [Wₓ : W Wₓ₀])
        (match* (Doms Wₓ)
          [('() '()) (values (hash ⊥ΔΣ {set '()}) ∅)]
          [((cons Dom Doms) (cons Vₓ Wₓ))
           (with-each-path [(ΔΣₓ Wₓ*s) (mon-dom Σ ctx Dom Vₓ)]
             (with-each-path [(ΔΣ* Ws*) (go (⧺ Σ ΔΣₓ) Doms Wₓ)]
               (just (cons (car (collapse-W^ Wₓ*s)) (collapse-W^ Ws*)) (⧺ ΔΣₓ ΔΣ*))))]
          [(_ _)
           (err (Blm l+ ℓ ℓₒ (map (compose1 (inst set V) Dom-ctc) Doms₀) Wₓ₀))])))

    (: mon-dom : Σ Ctx Dom V^ → (Values R (℘ Err)))
    (define (mon-dom Σ ctx dom V)
      (match-define (Dom x c ℓₓ) dom)
      (match c
        [(Clo (-var xs #f) E Ρ _)
         (define ΔΣ₀ (stack-copy Ρ Σ))
         (define Σ₀ (⧺ Σ ΔΣ₀))
         (with-each-path [(ΔΣ₁ Ws) (evl Σ₀ E)]
           (match-define (list C) (collapse-W^ Ws)) ; FIXME catch
           (with-each-path [(ΔΣ₂ Ws) (mon (⧺ Σ₀ ΔΣ₁) ctx C V)]
             (match-define (and W (list V*)) (collapse-W^ Ws)) ; FIXME catch
             (just W (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ (alloc (γ:lex x) V*)))))]
        [(? α? α)
         (with-each-path [(ΔΣ Ws) (mon Σ ctx (@ α) V)]
           (match-define (and W (list V*)) (collapse-W^ Ws))
           (just W (⧺ ΔΣ (alloc (γ:lex x) V*))))]))

    (define Dom-ref (match-lambda [(Dom x _ _) {set (γ:lex x)}]))

    (define (with-result [ΔΣ-acc : ΔΣ] [comp : (→ (Values R (℘ Err)))])
      (if Rngs
          (with-each-path [(ΔΣₐ Wₐs) (comp)]
            (with-pre (⧺ ΔΣ-acc ΔΣₐ) (mon-doms (⧺ Σ₀ ΔΣ-acc ΔΣₐ) ctx Rngs (collapse-W^ Wₐs))))
          (with-pre ΔΣ-acc (comp))))

    (with-guarded-arity Wₓ G ℓ
      [Wₓ
       #:when (and (not ?Doms:rest) (= (length Wₓ) (length Doms)))
       (with-each-path [(ΔΣₓ _) (mon-doms Σ₀ (Ctx-flip ctx) Doms Wₓ)]
         (define args (map Dom-ref Doms))
         (with-result ΔΣₓ (λ () (app (⧺ Σ₀ ΔΣₓ) ℓ (@ αₕ) args))))]
      [Wₓ
       #:when (and ?Doms:rest (>= (length Wₓ) (length Doms)))
       (define-values (W₀ Wᵣ) (split-at Wₓ (length Doms)))
       (define ctx* (Ctx-flip ctx))
       (with-each-path [(ΔΣ-init _) (mon-doms Σ₀ ctx* Doms W₀)]
         (define-values (Vᵣ ΔΣᵣ) (alloc-rest (Dom-loc ?Doms:rest) Wᵣ))
         (with-each-path [(ΔΣ-rest _) (mon-dom (⧺ Σ₀ ΔΣ-init ΔΣᵣ) ctx* ?Doms:rest Vᵣ)]
           (define args-init (map Dom-ref Doms))
           (define arg-rest (Dom-ref ?Doms:rest))
           (with-result (⧺ ΔΣ-init ΔΣᵣ ΔΣ-rest)
             (λ () (app/rest (⧺ Σ₀ ΔΣ-init ΔΣᵣ ΔΣ-rest) ℓ (@ αₕ) args-init arg-rest)))))]))

  (: app-∀/C : Ctx ∀/C α → ⟦F⟧)
  (define ((app-∀/C ctx G α) Σ ℓ Wₓ)
    ???)

  (: app-Case-=> : Ctx Case-=> α → ⟦F⟧)
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
       (with-each-path [(ΔΣ₁ W₁s) (app Σ ℓ (unpack α₁ Σ) Wₓ)]
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values (collapse-W^ W₁s)
           (λ (_ ΔΣ*) (with-pre (⧺ ΔΣ₁ ΔΣ*) (app (⧺ Σ₁ ΔΣ*) ℓ (unpack α₂ Σ) Wₓ)))
           (λ (_ ΔΣ*) (values (hash (⧺ ΔΣ₁ ΔΣ*) {set (list {set -ff})}) ∅))))]))

  (: app-Or/C : α α ℓ → ⟦F⟧)
  (define ((app-Or/C α₁ α₂ ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-path [(ΔΣ₁ W₁s) (app Σ ℓ (unpack α₁ Σ) Wₓ)]
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values (collapse-W^ W₁s)
           (λ (_ ΔΣ*) (values (hash (⧺ ΔΣ₁ ΔΣ*) W₁s) ∅))
           (λ (_ ΔΣ*) (with-pre (⧺ ΔΣ₁ ΔΣ*) (app (⧺ Σ₁ ΔΣ*) ℓ (unpack α₂ Σ) Wₓ)))))]))

  (: app-Not/C : α ℓ → ⟦F⟧)
  (define ((app-Not/C α ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-path [(ΔΣ Ws) (app Σ ℓ (unpack α Σ) Wₓ)]
         (define Σ* (⧺ Σ ΔΣ))
         (with-split-Σ Σ* 'values (collapse-W^ Ws)
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
         (with-each-path [(ΔΣₜ Wₜs) (app (⧺ Σ ΔΣᵢ) ℓ (unpack α Σ) (collapse-W^ Wᵢs))]
           (define ΔΣ (⧺ ΔΣᵢ ΔΣₜ))
           (define Σ* (⧺ Σ ΔΣ))
           (with-split-Σ Σ* 'values (collapse-W^ Wₜs)
             (λ _ (with-pre ΔΣ ((app-St/C-fields 𝒾 (assert (+ 1 i) index?) αs ℓₕ) Σ* ℓ Vₓ)))
             (λ _ (just -ff ΔΣ)))))]))

  (: app-opq : (℘ P) → ⟦F⟧)
  (define ((app-opq Ps) Σ ℓ Wₓ)
    (define n (length Wₓ))
    (define es
      (let ([ℓₒ (ℓ-with-src +ℓ₀ 'Λ)]
            [Vₕ {set (-● Ps)}])
        (cond
          [(not (∋ Ps 'procedure?))
           {set (Blm (ℓ-src ℓ) ℓ ℓₒ (list {set 'procedure?}) (list Vₕ))}]
          [(not (eq? '✓ (sat Σ (P:arity-includes n) {set (-● Ps)})))
           {set (Blm (ℓ-src ℓ) ℓ ℓₒ (list {set (P:arity-includes n)}) (list Vₕ))}]
          [else ∅])))
    (define αₕᵥ (γ:hv #f))
    (define ΔΣ*
      (let ([ΔΣ:leak (alloc αₕᵥ (collect-behavioral-values {set Wₓ} Σ))]
            [ΔΣ:field-leaks
             (for*/fold ([acc : ΔΣ ⊥ΔΣ]) ([Vs (in-list Wₓ)] [V (in-set Vs)])
               (match V
                 [(St 𝒾 αs)
                  ;; Bucket values by fields, breaking correlation between fields
                  (for/fold ([acc : ΔΣ acc]) ([αᵢ (in-list αs)] [i (in-naturals)])
                    (⧺ acc (alloc (γ:escaped-field 𝒾 (assert i index?)) (unpack αᵢ Σ))))]
                 [(Guarded ctx (St/C 𝒾 αs _) αᵥ) ; FIXME
                  acc]
                 [_ acc]))])
        (⧺ ΔΣ:leak ΔΣ:field-leaks)))
    (define-values (r* es*) (hv (⧺ Σ ΔΣ*) αₕᵥ))
    (values (ΔΣ⧺R ΔΣ* r*) (∪ es es*)))

  (: app-= : (U T -b) → ⟦F⟧)
  (define ((app-= T) Σ ℓ Wₓ) ((app-prim 'equal?) Σ ℓ (cons {set T} Wₓ)))

  (: app-err : V → ⟦F⟧)
  (define ((app-err V) Σ ℓ Wₓ)
    (err (Blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'procedure?}) (list {set V}))))

  (: app/rest : Σ ℓ V^ W V^ → (Values R (℘ Err)))
  (define (app/rest Σ ℓ Vₕ^ Wₓ Vᵣ)
    (define args:root (∪ (W-root Wₓ) (V^-root Vᵣ)))
    ((inst fold-ans V)
     (λ (Vₕ)
       (define root (∪ args:root (V-root Vₕ)))
       (define Σ* (gc root Σ))
       (ref-$! ($:Key:App/rest Σ* ℓ Vₕ Wₓ Vᵣ)
               (λ () (with-gc root (λ () (app₁/rest Σ* ℓ Vₕ Wₓ Vᵣ))))))
     (unpack Vₕ^ Σ)))

  (: app₁/rest : Σ ℓ V W V^ → (Values R (℘ Err)))
  (define (app₁/rest Σ ℓ V W₀ Vᵣ)
    (define f (match V
                [(? Clo? V) (app-Clo/rest V)]
                [(? Case-Clo? V) (app-Case-Clo/rest V)]
                [(-st-mk 𝒾) (app-st-mk/rest 𝒾)]
                [(-st-p 𝒾) (app-st-p/rest 𝒾)]
                [(-st-ac 𝒾 i) (app-st-ac/rest 𝒾 i)]
                [(-st-mut 𝒾 i) (app-st-mut/rest 𝒾 i)]
                [(? symbol? o) (app-prim/rest o)]
                [(Guarded ctx (? Fn/C? G) α)
                 (cond [(==>i? G)    (app-==>i/rest ctx G α)]
                       [(∀/C? G)     (app-∀/C/rest  ctx G α)]
                       [(Case-=>? G) (app-Case-=>/rest ctx G α)]
                       [else (app-Terminating/C/rest ctx α)])]
                [(And/C α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-And/C/rest α₁ α₂ ℓ)]
                [(Or/C  α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-Or/C/rest  α₁ α₂ ℓ)]
                [(Not/C α ℓ) (app-Not/C/rest α ℓ)]
                [(St/C 𝒾 αs ℓ) #:when (C-flat? V Σ) (app-St/C/rest 𝒾 αs ℓ)]
                [(-● Ps) (app-opq/rest Ps)]
                [V (app-err/rest V)]))
    (f Σ ℓ W₀ Vᵣ))

  (: app-Clo/rest : Clo → ⟦G⟧)
  (define ((app-Clo/rest clo) Σ ℓ W₀ Vᵣ)
    (match-define (Clo (-var xs₀ xᵣ) E Ρ ℓₕ) clo)
    (match (adjust-init-var-args Σ ℓ (length xs₀) (unpack-W W₀ Σ) Vᵣ)
      [(list W₀* Vᵣ* ΔΣ)
       (define ΔΣₓ (⧺ (stack-copy Ρ Σ)
                      (alloc-lex* xs₀ W₀*)
                      (if xᵣ (alloc-lex xᵣ Vᵣ*) ⊥ΔΣ)))
       (with-pre (⧺ ΔΣ ΔΣₓ) (evl (⧺ Σ ΔΣ ΔΣₓ) E))]
      [#f (err (Err:Arity ℓₕ `(,@W₀ ,Vᵣ) ℓ))]))
  
  (: app-Case-Clo/rest : Case-Clo → ⟦G⟧)
  (define ((app-Case-Clo/rest case-clo) Σ ℓ W₀ Vᵣ)
    ???)
  
  (: app-st-mk/rest : -𝒾 → ⟦G⟧)
  (define ((app-st-mk/rest 𝒾) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-st-p/rest : -𝒾 → ⟦G⟧)
  (define ((app-st-p/rest 𝒾) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-st-ac/rest : -𝒾 Index → ⟦G⟧)
  (define ((app-st-ac/rest 𝒾 i) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-st-mut/rest : -𝒾 Index → ⟦G⟧)
  (define ((app-st-mut/rest 𝒾 i) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-prim/rest : -o → ⟦G⟧)
  (define ((app-prim/rest o) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-==>i/rest : Ctx ==>i α → ⟦G⟧)
  (define ((app-==>i/rest ctx G α) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-∀/C/rest : Ctx ∀/C α → ⟦G⟧)
  (define ((app-∀/C/rest ctx G α) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-Case-=>/rest : Ctx Case-=> α → ⟦G⟧)
  (define ((app-Case-=>/rest ctx G α) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-Terminating/C/rest : Ctx α → ⟦G⟧)
  (define ((app-Terminating/C/rest ctx α) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-And/C/rest : α α ℓ → ⟦G⟧)
  (define ((app-And/C/rest α₁ α₂ ℓ) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-Or/C/rest : α α ℓ → ⟦G⟧)
  (define ((app-Or/C/rest α₁ α₂ ℓ) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-Not/C/rest : α ℓ → ⟦G⟧)
  (define ((app-Not/C/rest α ℓ) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-St/C/rest : -𝒾 (Listof α) ℓ → ⟦G⟧)
  (define ((app-St/C/rest 𝒾 αs ℓ) Σ ℓ W₀ Vᵣ)
    ???)

  (: app-opq/rest : (℘ P) → ⟦G⟧)
  (define ((app-opq/rest Ps) Σ ℓ W₀ Vᵣ) ((app-opq Ps) Σ ℓ `(,@W₀ ,Vᵣ)))
  
  (: app-err/rest : V → ⟦G⟧)
  (define ((app-err/rest V) Σ ℓ W₀ Vᵣ) ((app-err V) Σ ℓ `(,@W₀ ,Vᵣ)))

  (: adjust-init-var-args : Σ ℓ Natural W V^ → (Option (List W V^ ΔΣ)))
  (define (adjust-init-var-args Σ ℓ required-inits W₀ Vᵣ)
    (match (- required-inits (length W₀))
      [(? positive? remaining-inits)
       (match (unalloc-prefix remaining-inits Vᵣ Σ)
         [(cons W₁ Vᵣ*) (list (append W₀ W₁) Vᵣ* ⊥ΔΣ)]
         [#f #f])]
      [0 (list W₀ Vᵣ ⊥ΔΣ)]
      [(? negative?)
       (define-values (W₀* W₁) (split-at W₀ required-inits))
       (define-values (Vᵣ* ΔΣ) (alloc-rest ℓ W₁ #:tail Vᵣ))
       (list W₀* Vᵣ* ΔΣ)]))

  (: adjust-return : Σ ΔΣ -formals W R → R)
  (define (adjust-return Σ₀ ΔΣₓ fml Wₓ r)
    (define Σ₀* (⧺ Σ₀ ΔΣₓ))
    (define Σₑᵣ ((inst make-parameter Σ) Σ₀*)) ; HACK to reduce cluttering
    (define adjust-T (rename (trim-renamings Σ₀ (make-renamings fml Wₓ))))
    (define (go-ΔΣ [ΔΣ₀ : ΔΣ])
      (for*/hash : ΔΣ ([(T r) (in-hash ΔΣ₀)]
                       [T* (in-value (adjust-T T))] #:when T*)
        (values T* (cons (go-V^ (car r)) (cdr r)))))
    (define (go-W [W : W]) (map go-V^ W))
    (define (go-V^ [V^ : V^]) (set-union-map go-V V^))
    (define (go-V [V : V]) (if (T? V) (go-T V) {set V}))
    (define (go-T [T : T]) (cond [(adjust-T T) => set]
                                 [else (unpack T (Σₑᵣ))]))
    
    (for/fold ([acc : R ⊥R]) ([(ΔΣ Ws) (in-hash r)])
      (parameterize ([Σₑᵣ (⧺ Σ₀* ΔΣ)])
        (hash-update acc
                     (go-ΔΣ ΔΣ)
                     (λ ([Ws₀ : (℘ W)]) (∪ Ws₀ (map/set go-W Ws)))
                     mk-∅))))

  (: trim-renamings : Σ Renamings → Renamings)
  ;; Prevent some renaming from propagating based on what the caller has
  (define (trim-renamings Σ rn)
    (for/fold ([rn : Renamings rn])
              ([(x ?T) (in-hash rn)]
               ;; FIXME this erasure is too aggressive
               #:when (T:@? ?T))
      (hash-set rn x #f)))

  (define-simple-macro (with-guarded-arity W f ℓ [p body ...] ...)
    (match W
      [p body ...] ...
      [_ (err (Err:Arity f (length W) ℓ))]))
  
  )
