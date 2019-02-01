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
          prims^
          exec^ evl^ mon^ hv^ gc^)
  (export app^)

  (: app : Σ ℓ V^ W → (Values R (℘ Err)))
  (define (app Σ ℓ Vₕ^ W)
    (define W:root (W-root W))
    ((inst fold-ans V)
     (λ (Vₕ) (app₁ (gc (∪ W:root (V-root Vₕ)) Σ) ℓ Vₕ W))
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
                 (cond [(==>? G)     (app-==>  ctx G α)]
                       [(==>i? G)    (app-==>i ctx G α)]
                       [(∀/C? G)     (app-∀/C  ctx G α)]
                       [(Case-=>? G) (app-Case-=> ctx G α)]
                       [else (app-Terminating/C ctx α)])]
                [(And/C α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-And/C α₁ α₂ ℓ)]
                [(Or/C  α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-Or/C  α₁ α₂ ℓ)]
                [(Not/C α ℓ) (app-Not/C α ℓ)]
                [(One-Of/C bs) (app-One-Of/C bs)]
                [(St/C 𝒾 αs ℓ) #:when (C-flat? V Σ) (app-St/C 𝒾 αs ℓ)]
                [(-● Ps) (app-opq Ps)]
                [V (app-err V)]))
    (ref-$! ($:Key:App Σ ℓ V W) (λ () (f Σ ℓ W))))

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
           (with-pre ΔΣₓ (evl (⧺ Σ ΔΣₓ) E))]
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
         (λ (Wₓ* ΔΣ₂) (err (Blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set (-st-p 𝒾)}) Wₓ*))))]))

  (: unchecked-app-st-ac : -𝒾 Index → Σ ℓ V^ → (Values R (℘ Err)))
  (define ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)
    ((inst fold-ans V)
     (match-lambda
       [(St _ αs) (just (unpack (list-ref αs i) Σ))]
       [(? γ? γ) (just (T:@ (-st-ac 𝒾 i) (list γ)))]
       [(Guarded ctx (St/C _ αs ℓₕ) αᵥ)
        (with-collapsing/R [(ΔΣ Ws) ((unchecked-app-st-ac 𝒾 i) Σ ℓ (unpack αᵥ Σ))]
          (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (unpack (list-ref αs i) Σ) (car (collapse-W^ Ws)))))]
       [_ (just (-● ∅))])
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

  (: app-==> : Ctx ==> α → ⟦F⟧)
  (define ((app-==> ctx G αₕ) Σ ℓ Wₓ)
    (define (@ [α : α]) (unpack α Σ))
    (match-define (==> (-var Doms₀ Domᵣ) Rng ℓₕ) G)
    (define n (length Doms₀))
    (define ctx* (Ctx-with-site (Ctx-flip ctx) ℓ))
    (define (mon-Rng [ΔΣ : ΔΣ] [Wₐs : W^])
      (cond [Rng (define Σ* (⧺ Σ ΔΣ))
                 ((inst fold-ans W) (λ (Wₐ) (mon* Σ* ctx (map @ Rng) Wₐ)) Wₐs)]
            [else (values (hash ΔΣ Wₐs) ∅)]))
    (with-guarded-arity Wₓ ℓₕ ℓ
      [Wₓ
       #:when (and (not Domᵣ) (= (length Wₓ) n))
       (with-collapsing/R [(ΔΣₓ Ws) (mon* Σ ctx* (map @ Doms₀) Wₓ)]
         (define Wₓ* (collapse-W^ Ws))
         (with-each-path [(ΔΣₐ Wₐs) (app (⧺ Σ ΔΣₓ) ℓ (@ αₕ) Wₓ*)]
           (mon-Rng (⧺ ΔΣₓ ΔΣₐ) Wₐs)))]
      [Wₓ
       #:when (and Domᵣ (>= (length Wₓ) n))
       (define-values (W₀ Wᵣ) (split-at Wₓ n))
       (with-collapsing/R [(ΔΣ₀ W₀s) (mon* Σ ctx* (map @ Doms₀) W₀)]
         (define W₀* (collapse-W^ W₀s))
         (define-values (Vᵣ ΔΣᵣ) (alloc-rest ℓₕ Wᵣ))
         (with-collapsing/R [(ΔΣ₁ Wᵣ*) (mon (⧺ Σ ΔΣ₀ ΔΣᵣ) ctx* (@ Domᵣ) Vᵣ)]
           (with-each-path [(ΔΣₐ Wₐs) (app/rest (⧺ Σ ΔΣ₀ ΔΣᵣ ΔΣ₁) ℓ (@ αₕ) W₀* (car (collapse-W^ Wᵣ*)))]
             (mon-Rng (⧺ ΔΣ₀ ΔΣᵣ ΔΣ₁ ΔΣₐ) Wₐs))))]))

  (: app-==>i : Ctx ==>i α → ⟦F⟧)
  (define ((app-==>i ctx G αₕ) Σ₀ ℓ Wₓ)
    (match-define (==>i Doms Rng) G)
    (define (@ [α : α]) (lookup α Σ₀))

    (: mon-doms : Σ Ctx (Listof Dom) W → (Values R (℘ Err)))
    (define (mon-doms Σ ctx Doms Wₓ)
      (match* (Doms Wₓ)
        [('() '()) (values (hash ⊥ΔΣ {set '()}) ∅)]
        [((cons Dom Doms) (cons Vₓ Wₓ))
         (with-each-path [(ΔΣₓ Wₓ*s) (mon-dom Σ ctx Dom Vₓ)]
           (with-each-path [(ΔΣ* Ws*) (mon-doms (⧺ Σ ΔΣₓ) ctx Doms Wₓ)]
             (values (hash (⧺ ΔΣₓ ΔΣ*) {set (cons (car (collapse-W^ Wₓ*s)) (collapse-W^ Ws*))}) ∅)))]))

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
             (values (hash (⧺ ΔΣ₀ ΔΣ₁ ΔΣ₂ (alloc (γ:lex x) V*)) {set W}) ∅)))]
        [(? α? α)
         (with-each-path [(ΔΣ Ws) (mon Σ ctx (@ α) V)]
           (match-define (and W (list V*)) (collapse-W^ Ws))
           (values (hash (⧺ ΔΣ (alloc (γ:lex x) V*)) {set W}) ∅))]))
    
    (with-guarded-arity Wₓ G ℓ
      [Wₓ
       #:when (= (length Wₓ) (length Doms))
       (with-each-path [(ΔΣₓ Wₓ*) (mon-doms Σ₀ (Ctx-flip ctx) Doms Wₓ)]
         (with-each-path [(ΔΣₐ Wₐs) (app (⧺ Σ₀ ΔΣₓ) ℓ (@ αₕ)
                                         (map (compose1 (inst set γ) (compose1 γ:lex Dom-name)) Doms))]
           (mon-dom (⧺ Σ₀ ΔΣₓ ΔΣₐ) ctx Rng (car (collapse-W^ Wₐs)))))]))

  (: app-∀/C : Ctx ∀/C α → ⟦F⟧)
  (define ((app-∀/C ctx G α) Σ ℓ Wₓ)
    ???)

  (: app-Case-=> : Ctx Case-=> α → ⟦F⟧)
  (define ((app-Case-=> ctx G α) Σ ℓ Wₓ)
    (define n (length Wₓ))
    (match-define (Case-=> Cs) G)
    (match ((inst findf ==>)
            (match-lambda [(==> doms _ _) (arity-includes? (shape doms) n)])
            Cs)
      [(? values C) ((app-==> ctx C α) Σ ℓ Wₓ)]
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
         (λ (Wₓ* ΔΣ*) ((app-St/C-fields 𝒾 0 αs ℓₕ) Σ ℓ (car Wₓ*)))
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
             (λ (_ ΔΣ*) (with-pre ΔΣ ((app-St/C-fields 𝒾 (assert (+ 1 i) index?) αs ℓₕ) Σ* ℓ Vₓ)))
             (λ (_ ΔΣ*) (just -ff ΔΣ*)))))]))

  (: app-opq : (℘ P) → ⟦F⟧)
  (define ((app-opq Ps) Σ ℓ Wₓ)
    (define n (length Wₓ))
    (define es (if (∋ Ps 'procedure?)
                   (Blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'procedure?}) (list {set (-● ∅)}))
                   ∅))
    (define αₕᵥ (γ:hv #f))
    (define ΔΣ:leak (alloc αₕᵥ (collect-behavioral-values {set Wₓ} Σ)))
    (with-pre ΔΣ:leak (hv (⧺ Σ ΔΣ:leak) αₕᵥ)))

  (: app-err : V → ⟦F⟧)
  (define ((app-err V) Σ ℓ Wₓ)
    (err (Blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'procedure?}) (list {set V}))))

  (: app/rest : Σ ℓ V^ W V^ → (Values R (℘ Err)))
  (define (app/rest Σ ℓ Vₕ^ Wₓ Vᵣ)
    (define args:root (∪ (W-root Wₓ) (V^-root Vᵣ)))
    ((inst fold-ans V)
     (λ (Vₕ) (app₁/rest (gc (∪ args:root (V-root Vₕ)) Σ) ℓ Vₕ Wₓ Vᵣ))
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
                 (cond [(==>? G)     (app-==>/rest  ctx G α)]
                       [(==>i? G)    (app-==>i/rest ctx G α)]
                       [(∀/C? G)     (app-∀/C/rest  ctx G α)]
                       [(Case-=>? G) (app-Case-=>/rest ctx G α)]
                       [else (app-Terminating/C/rest ctx α)])]
                [(And/C α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-And/C/rest α₁ α₂ ℓ)]
                [(Or/C  α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-Or/C/rest  α₁ α₂ ℓ)]
                [(Not/C α ℓ) (app-Not/C/rest α ℓ)]
                [(St/C 𝒾 αs ℓ) #:when (C-flat? V Σ) (app-St/C/rest 𝒾 αs ℓ)]
                [(-● Ps) (app-opq/rest Ps)]
                [V (app-err/rest V)]))
    (ref-$! ($:Key:App/rest Σ ℓ V W₀ Vᵣ) (λ () (f Σ ℓ W₀ Vᵣ))))

  (: app-Clo/rest : Clo → ⟦G⟧)
  (define ((app-Clo/rest clo) Σ ℓ W₀ Vᵣ)
    (match-define (Clo (-var xs₀ xᵣ) E Ρ ℓₕ) clo)
    (match (adjust-args Σ ℓ (length xs₀) (unpack-W W₀ Σ) Vᵣ)
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

  (: app-==>/rest : Ctx ==> α → ⟦G⟧)
  (define ((app-==>/rest ctx G α) Σ ℓ W₀ Vᵣ)
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

  (: adjust-args : Σ ℓ Natural W V^ → (Option (List W V^ ΔΣ)))
  (define (adjust-args Σ ℓ required-inits W₀ Vᵣ)
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

  (define-simple-macro (with-guarded-arity W f ℓ [p body ...] ...)
    (match W
      [p body ...] ...
      [_ (err (Err:Arity f (length W) ℓ))]))
  
  )
