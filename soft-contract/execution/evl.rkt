#lang typed/racket/base

(provide evl@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/set
         racket/list
         racket/match
         typed/racket/unit
         (only-in typed-racket-hacks/unsafe unsafe-cast)
         syntax/parse/define
         set-extras
         unreachable
         "../utils/map.rkt"
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit evl@
  (import meta-functions^ static-info^ ast-pretty-print^
          sto^ cache^ val^ pretty-print^
          exec^ app^ mon^ gc^)
  (export evl^)

  (define evl-prog : (-prog → (Values (Option ΔΣ) (℘ Err)))
    (match-lambda
      [(-prog ms) (evl*/discard/collapse evl-module ⊥Σ ms)]))

  (: evl-module : Σ -module → (Values (Option ΔΣ) (℘ Err)))
  (define (evl-module Σ m)
    (parameterize ([current-module (-module-path m)])
      (evl*/discard/collapse evl-module-level-form Σ (-module-body m))))

  (: evl-module-level-form : Σ -module-level-form → (Values (Option ΔΣ) (℘ Err)))
  (define (evl-module-level-form Σ d)
    (match d
      [(-provide specs) (evl*/discard/collapse evl-spec Σ specs)]
      [(? -require?) (values ⊥ΔΣ ∅)]
      [(-define-values Xs E ℓ)
       (with-collapsing [(ΔΣ rhs) (evl/arity Σ E (length Xs) ℓ)]
         (define l (current-module))
         (define lhs (map (λ ([x : Symbol]) (-𝒾 x l)) Xs))
         (values (⧺ ΔΣ (alloc-lex* lhs (collapse-W^ rhs))) ∅))]
      [(? -e? E) (define-values (r es) (evl Σ E))
                 (values (collapse-R/ΔΣ r) es)]))

  (: evl-spec : Σ -provide-spec → (Values (Option ΔΣ) (℘ Err)))
  (define (evl-spec Σ spec)
    (match spec
      [(-p/c-item x c ℓ)
       (define l (current-module))
       (define 𝒾 (-𝒾 x l))
       (define α  (γ:top 𝒾))
       (define α* (γ:wrp 𝒾))
       (with-collapsed [(cons C^ ΔΣ) ((evl/single/collapse ℓ) Σ c)]
         (with-collapsing [(ΔΣ* Ws) (mon Σ (Ctx l 'dummy- ℓ ℓ) C^ (unpack α Σ))]
           (values (⧺ ΔΣ ΔΣ* (alloc α* (car (collapse-W^ Ws)))) ∅)))]
      [(? symbol? x)
       (define 𝒾 (-𝒾 x (current-module)))
       (define α  (γ:top 𝒾))
       (define α* (γ:wrp 𝒾))
       (values (alloc α* (lookup α Σ)) ∅)]))

  (: evl : Σ E → (Values R (℘ Err)))
  (define (evl Σ E₀)
    #;(printf "~a~a ⊢ ~a ⇓ ...~n"
            (make-string (* 2 (db:depth)) #\space)
            (show-Σ Σ)
            (show-e E₀))
    (parameterize ([db:depth (+ 1 (db:depth))])
      (match E₀
        [(? -prim? p) (just p)]
        [(-•) (just (-● ∅))]
        [(-λ Xs E ℓ)
         (define-values (Ρ ΔΣ) (close Σ (fv E₀)))
         (just (Clo Xs E Ρ ℓ) ΔΣ)]
        [(-case-λ cases ℓ)
         (define-values (Cases ΔΣ) (evl/special Σ cases Clo?))
         (just (Case-Clo Cases ℓ) ΔΣ)]
        [(-x x ℓ)
         (define-values (α modify-V)
           (cond [(symbol? x)
                  (values (γ:lex x) (inst values V))]
                 [(equal? (ℓ-src ℓ) (-𝒾-src x))
                  (values (γ:top x) (inst values V))]
                 [else
                  (values (γ:wrp x)
                          (if (symbol? (-𝒾-src x))
                              (λ ([V : V]) (with-negative-party (ℓ-src ℓ) V))
                              (λ ([V : V]) (with-positive-party 'dummy+
                                             (with-negative-party (ℓ-src ℓ) V)))))]))
         (define res (map/set modify-V (lookup α Σ)))
         (define r (R-of (if (set? res) (set-remove res -undefined) res)))
         (define es (if (∋ (unpack res Σ) -undefined)
                        {set (Err:Undefined (if (-𝒾? x) (-𝒾-name x) x) ℓ)}
                        ∅))
         (values r es)]
        [(-@ f xs ℓ)
         (with-each-path [(ΔΣₕ Wsₕ) (evl/arity Σ f 1 ℓ)]
           (match-define (list V^ₕ) (collapse-W^ Wsₕ))
           (with-collapsed/R [(cons Wₓ ΔΣₓ) (evl*/collapse (evl/single/collapse ℓ) (⧺ Σ ΔΣₕ) xs)]
             (with-pre (⧺ ΔΣₕ ΔΣₓ) (app (⧺ Σ ΔΣₕ ΔΣₓ) ℓ V^ₕ Wₓ))))]
        [(-if E E₁ E₂ ℓ)
         (with-each-path [(ΔΣ Ws) (evl/arity Σ E 1 ℓ)]
           (define Σ* (⧺ Σ ΔΣ))
           (with-split-Σ Σ* 'values (collapse-W^ Ws)
             (λ (_ ΔΣ₁) (with-pre (⧺ ΔΣ ΔΣ₁) (evl (⧺ Σ* ΔΣ₁) E₁)))
             (λ (_ ΔΣ₂) (with-pre (⧺ ΔΣ ΔΣ₂) (evl (⧺ Σ* ΔΣ₂) E₂)))))]
        [(-wcm k v e) (error 'TODO "with-current-continuation-mark")]
        [(-begin Es)
         (match Es
           ['() (just -void)] ; unreachable if `begin` is in expr position
           [_
            (match-define-values (Es₀ (list Eₙ)) (split-at Es (sub1 (length Es))))
            (with-collapsed/R [ΔΣ₀ (evl*/discard/collapse evl/discard/collapse Σ Es₀)]
              (with-pre ΔΣ₀ (evl (⧺ Σ ΔΣ₀) Eₙ)))])]
        [(-begin0 E Es)
         (define-values (r₀ es₀) (evl Σ E))
         (match (collapse-R/ΔΣ r₀)
           [(? values ΔΣ₀)
            (with-collapsed/R [ΔΣ* (evl*/discard/collapse evl/discard/collapse (⧺ Σ ΔΣ₀) Es)]
              (values (R⧺ΔΣ r₀ ΔΣ*) es₀))]
           [#f (values ⊥R es₀)])]
        [(-quote b) (if (Base? b) (just (-b b)) (error 'TODO "(quote ~a)" b))]
        [(-let-values bnds E ℓ)
         (define-values (ΔΣₓs es) (evl-bnd* Σ ℓ bnds))
         (for/fold ([r : R ⊥R] [es : (℘ Err) es])
                   ([ΔΣₓ : ΔΣ (in-set ΔΣₓs)])
           (with-pre ΔΣₓ (evl (⧺ Σ ΔΣₓ) E)))]
        [(-letrec-values bnds E ℓ)
         (define ΔΣ₀
           (for*/fold ([ΔΣ₀ : ΔΣ ⊥ΔΣ])
                      ([bnd (in-list bnds)]
                       [x (in-list (Binding-lhs bnd))])
             (⧺ ΔΣ₀ (alloc-lex x {set -undefined}))))
         (with-collapsed/R [ΔΣₓ (evl*/discard/collapse (evl-set-bnd ℓ) (⧺ Σ ΔΣ₀) bnds)]
           (define ΔΣ* (⧺ ΔΣ₀ ΔΣₓ))
           (with-pre ΔΣ* (evl (⧺ Σ ΔΣ*) E)))]
        [(-set! X E ℓ)
         (with-collapsing/R [(ΔΣ:rhs rhs) (evl/arity Σ E 1 ℓ)]
           (define α (if (symbol? X) (γ:lex X) (γ:top X)))
           (define ΔΣ*
             (for/fold ([ΔΣ* : ΔΣ ΔΣ:rhs]) ([α (in-set (car (hash-ref Σ α (λ () !!!))))])
               (match α
                 [(α:dyn (β:mut (== X)) _) (⧺ ΔΣ* (mut α (car (collapse-W^ rhs))))]
                 [α (error 'internal "~a ↦ ~a" X α)])))
           (just -void ΔΣ*))]
        [(-error s ℓ) (err (Err:Raised s ℓ))]
        [(-μ/c x E)
         (with-collapsed/R [(cons C ΔΣ) ((evl/single/collapse +ℓ₀) Σ E)]
           (define α (α:dyn (β:x/c x) H₀))
           (values (hash (⧺ ΔΣ (alloc α C)) {set (list {set α})}) ∅))]
        [(--> (-var c:init ?c:rest) d ℓ)
         (with-collapsed/R ((cons Cs ΔΣ₁)
                            (evl*/collapse
                             (evl/single/collapse ℓ)
                             Σ `(,@c:init ,@(if ?c:rest (list ?c:rest) '()))))
           (with-each-path ((ΔΣ₂ D) (evl (⧺ Σ ΔΣ₁) d))
             (define-values (A ΔΣ₃)
               (if ?c:rest
                   (match-let-values ([(C:init (list C:rest))
                                       (split-at Cs (sub1 (length Cs)))])
                     (mk-==> C:init C:rest D ℓ))
                   (mk-==> Cs #f D ℓ)))
             (just A (⧺ ΔΣ₁ ΔΣ₂ ΔΣ₃))))]
        [(-->i doms rng)
         (with-collapsed/R [(cons W ΔΣ₀) (evl*/collapse evl-dom Σ `(,@doms ,rng))]
           (: on-C : (→ β) ΔΣ Symbol (U Clo V^) ℓ → (Values Dom ΔΣ))
           (define (on-C mk-β ΔΣ x C ℓ)
             (cond [(Clo? C) (values (Dom x C ℓ) ΔΣ)]
                   [else (define α (α:dyn (mk-β) H₀))
                         (values (Dom x α ℓ) (⧺ ΔΣ (alloc α C)))]))
           (match-define-values (Cs (list D)) (split-at W (sub1 (length W))))
           (define-values (Doms-rev ΔΣ₁)
             (for/fold ([Doms-rev : (Listof Dom) '()] [ΔΣ : ΔΣ ΔΣ₀])
                       ([domᵢ (in-list doms)] [Cᵢ (in-list Cs)] [i : Natural (in-naturals)])
               (match-define (-dom xᵢ _ _ ℓᵢ) domᵢ)
               (define-values (Dom ΔΣ*) (on-C (λ _ (β:dom ℓᵢ i)) ΔΣ xᵢ Cᵢ ℓᵢ))
               (values (cons Dom Doms-rev) ΔΣ*)))
           (define-values (Rng ΔΣ₂)
             (match-let ([(-dom xᵣ _ _ ℓᵣ) rng])
               (on-C (λ _ (β:rng ℓᵣ 1 0)) ΔΣ₁ xᵣ D ℓᵣ)))
           (values (hash ΔΣ₂ {set (list {set (==>i (reverse Doms-rev) Rng)})})
                   ∅))]
        [(case--> cases)
         (define-values (Cases ΔΣ) (evl/special Σ cases ==>?))
         (just (Case-=> Cases) ΔΣ)]
        [(-x/c x) (just (α:dyn (β:x/c x) H₀))]
        [(-∀/c xs E)
         (define-values (Ρ ΔΣ) (close Σ (fv E₀)))
         (just (∀/C xs E Ρ) ΔΣ)])))

  (: evl-bnd* : Σ ℓ (Listof Binding) → (Values (℘ ΔΣ) (℘ Err)))
  (define (evl-bnd* Σ₀ ℓ bnds)
    (: evl-bnd : Σ Binding → (Values (℘ ΔΣ) (℘ Err)))
    (define (evl-bnd Σ bnd)
      (match-define (mk-Binding xs E) bnd)
      (define-values (r es) (evl/arity Σ E (length xs) ℓ))
      (define ΔΣs (for/set: : (℘ ΔΣ) ([(ΔΣ rhs) (in-hash r)])
                    (⧺ ΔΣ (alloc-lex* xs (collapse-W^ rhs)))))
      (values ΔΣs es))

    (let step ([Σ : Σ Σ₀] [bnds : (Listof Binding) bnds])
      (match bnds
        ['() (values {set ⊥ΔΣ} ∅)]
        [(cons bnd₀ bnds*)
         (define-values (ΔΣ₀s es₀) (evl-bnd Σ bnd₀))
         (for/fold ([ΔΣs* : (℘ ΔΣ) ∅] [es : (℘ Err) es₀])
                   ([ΔΣ₀ : ΔΣ (in-set ΔΣ₀s)])
           (define-values (ΔΣ₁s es₁) (step (⧺ Σ ΔΣ₀) bnds*))
           (values (for/set: : (℘ ΔΣ) ([ΔΣ₁ : ΔΣ (in-set ΔΣ₁s)])
                     (⧺ ΔΣ₀ ΔΣ₁))
                   (∪ es es₁)))])))

  (: evl-set-bnd : ℓ → Σ Binding → (Values (Option ΔΣ) (℘ Err)))
  ;; Run let-rec binding where the addresses have already been allocated
  (define ((evl-set-bnd ℓ) Σ bnd)
    (match-define (mk-Binding xs E) bnd)
    (: mut-lex : Symbol V^ ΔΣ → ΔΣ)
    (define (mut-lex x V^ ΔΣ) (⧺ ΔΣ (mut (resolve-lex x) V^)))
    (with-collapsing [(ΔΣ rhs) (evl/arity Σ E (length xs) ℓ)]
      (values (foldl mut-lex ΔΣ xs (collapse-W^ rhs)) ∅)))

  (: evl-dom : Σ -dom → (Values (Option (Pairof (U Clo V^) ΔΣ)) (℘ Err)))
  (define (evl-dom Σ dom)
    (match-define (-dom _ ?deps c ℓ) dom)
    (if ?deps
        (let-values ([(Ρ ΔΣ) (close Σ (set-subtract (fv c) (list->seteq ?deps)))])
          (values (cons (Clo (-var ?deps #f) c Ρ ℓ) ΔΣ) ∅))
        ((evl/single/collapse ℓ) Σ c)))

  (: evl/arity : Σ E Natural ℓ → (Values R (℘ Err)))
  ;; Run expression with arity guard
  (define (evl/arity Σ E n ℓ)
    (define-values (r es) (evl Σ E))
    (for/fold ([r* : R r] [es* : (℘ Err) es]) ([(ΔΣ Ws) (in-hash r)])
      (define-values (Ws:ok Ws:er) ((inst set-partition W) (λ (W) (= n (length W))) Ws))
      (define (es**) (set-add es* (Err:Values n E (collapse-W^ Ws:er) ℓ)))
      (cond [(set-empty? Ws:er) (values r* es*)]
            [(set-empty? Ws:ok) (values (hash-remove r* ΔΣ) (es**))]
            [else (values (hash-set r* ΔΣ Ws:ok) (es**))])))

  (: evl/discard/collapse : Σ E → (Values (Option ΔΣ) (℘ Err)))
  ;; Run expression for collapsed side-effect
  (define (evl/discard/collapse Σ E)
    (define-values (r es) (evl Σ E))
    (values (collapse-R/ΔΣ r) es)) 

  (: evl/single/collapse : ℓ → Σ E → (Values (Option (Pairof V^ Σ)) (℘ Err)))
  (define ((evl/single/collapse ℓ) Σ E)
    (with-collapsing [(ΔΣ Ws) (evl/arity Σ E 1 ℓ)]
      (values (cons (car (collapse-W^ Ws)) ΔΣ) ∅)))

  (: evl/special (∀ (X) Σ (Listof E) (V → Boolean : X) → (Values (Listof X) ΔΣ)))
  (define (evl/special Σ Es p?)
    (define-values (Xs-rev ΔΣ*)
      (for/fold ([Xs-rev : (Listof X) '()] [ΔΣ : ΔΣ ⊥ΔΣ]) ([E (in-list Es)])
        (define-values (rᵢ esᵢ) (evl Σ E))
        (assert (set-empty? esᵢ))
        (match-define (list (cons ΔΣᵢ Wsᵢ)) (hash->list rᵢ))
        (values (cons (assert (set-first (car (set-first Wsᵢ))) p?) Xs-rev) (⧺ ΔΣ ΔΣᵢ))))
    (values (reverse Xs-rev) ΔΣ*))

  (: evl*/discard/collapse
     (∀ (X) (Σ X → (Values (Option ΔΣ) (℘ Err))) Σ (Listof X) → (Values (Option ΔΣ) (℘ Err))))
  ;; Run sequence for collapsed side-effects
  (define (evl*/discard/collapse f Σ₀ xs)
    (let loop ([acc-ΔΣ : ΔΣ ⊥ΔΣ] [acc-es : (℘ Err) ∅] [Σ : Σ Σ₀] [xs xs])
      (match xs
        ['() (values acc-ΔΣ acc-es)]
        [(cons x₁ xs*)
         (define-values (ΔΣ₁ es₁) (f Σ x₁))
         (if ΔΣ₁
             (loop (⧺ acc-ΔΣ ΔΣ₁) (∪ acc-es es₁) (⧺ Σ ΔΣ₁) xs*)
             (values #f (∪ acc-es es₁)))]))) 

  (: evl*/collapse (∀ (X Y)
                      (Σ X → (Values (Option (Pairof Y ΔΣ)) (℘ Err)))
                      Σ (Listof X) →
                      (Values (Option (Pairof (Listof Y) ΔΣ)) (℘ Err))))
  (define (evl*/collapse ev Σ₀ xs)
    (let loop ([acc-ΔΣ : ΔΣ ⊥ΔΣ]
               [acc-rev-ys : (Listof Y) '()]
               [acc-es : (℘ Err) ∅]
               [Σ : Σ Σ₀]
               [xs xs])
      (match xs
        ['() (values (cons (reverse acc-rev-ys) acc-ΔΣ) acc-es)]
        [(cons x₁ xs*)
         (match/values (ev Σ x₁)
           [((cons y₁ ΔΣ₁) es)
            (loop (⧺ acc-ΔΣ ΔΣ₁)
                  (cons y₁ acc-rev-ys)
                  (∪ acc-es es)
                  (⧺ Σ ΔΣ₁)
                  xs*)]
           [(#f es) (values #f (∪ acc-es es))])])))

  (: mk-==> : W (Option V^) W^ ℓ → (Values V^ ΔΣ))
  (define (mk-==> dom:init ?dom:rest rngs ℓ)
    (define-values (αs:dom ΔΣ:dom) (alloc-each dom:init (λ (i) (β:dom ℓ i))))
    (define-values (α:rest ΔΣ:rest)
      (if ?dom:rest
          (let ([α (α:dyn (β:rst ℓ) H₀)])
            (values α (alloc α ?dom:rest)))
          (values #f ⊥ΔΣ)))
    (define Dom (-var αs:dom α:rest))
    (for/fold ([Vs : V^ ∅] [ΔΣ* : ΔΣ (⧺ ΔΣ:dom ΔΣ:rest)])
              ([(n D) (in-hash (collapse-W^-by-arities rngs))])
      (define-values (αs:rng ΔΣ:rng)
        (match D
          [(list {singleton-set 'any}) (values #f ⊥ΔΣ)]
          [_ (alloc-each D (λ (i) (β:rng ℓ n i)))]))
      (values (set-add Vs (==> Dom αs:rng ℓ)) (⧺ ΔΣ* ΔΣ:rng)))) 
  )
