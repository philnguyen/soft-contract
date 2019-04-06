#lang typed/racket/base

(provide evl@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/set
         racket/list
         racket/match
         racket/vector
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

  (define evl-prog : (-prog → (Option ΔΣ))
    (match-lambda
      [(-prog ms) (evl*/discard/collapse evl-module ⊥Σ ms)]))

  (: evl-module : Σ -module → (Option ΔΣ))
  (define (evl-module Σ m)
    (parameterize ([current-module (-module-path m)])
      (evl*/discard/collapse evl-module-level-form Σ (-module-body m))))

  (: evl-module-level-form : Σ -module-level-form → (Option ΔΣ))
  (define (evl-module-level-form Σ d)
    (match d
      [(-provide specs) (evl*/discard/collapse evl-spec Σ specs)]
      [(? -require?) ⊥ΔΣ]
      [(-define-values Xs E ℓ)
       (with-collapsing [(ΔΣ rhs) (evl/arity Σ E (length Xs) ℓ)]
         (define l (current-module))
         (define lhs (map (λ ([x : Symbol]) (-𝒾 x l)) Xs))
         (⧺ ΔΣ (alloc-lex* lhs (collapse-W^ rhs))))]
      [(? -module? m) (evl-module Σ m)]
      [(? -e? E) (collapse-R/ΔΣ (evl Σ E))]))

  (: evl-spec : Σ -provide-spec → (Option ΔΣ))
  (define (evl-spec Σ spec)
    (match spec
      [(-p/c-item x c ℓ)
       (define l (current-module))
       (define 𝒾 (-𝒾 x l))
       (define α  (γ:top 𝒾))
       (define α* (γ:wrp 𝒾))
       (with-collapsed [(cons C^ ΔΣ) ((evl/single/collapse ℓ) Σ c)]
         (with-collapsing [(ΔΣ* Ws) (mon (⧺ Σ ΔΣ) (Ctx l 'dummy- ℓ ℓ) C^ (unpack α Σ))]
           (⧺ ΔΣ ΔΣ* (alloc α* (car (collapse-W^ Ws))))))]
      [(? symbol? x)
       (define 𝒾 (-𝒾 x (current-module)))
       (define α  (γ:top 𝒾))
       (define α* (γ:wrp 𝒾))
       (alloc α* (lookup α Σ))]))

  (: evl : Σ E → R)
  (define (evl Σ E)
    (define root (E-root E))
    (define Σ* (gc root Σ))
    (ref-$! ($:Key:Exp Σ* E) (λ () (gc-R root Σ* (do-evl Σ* E)))))

  (: do-evl : Σ E → R)
  ;; Evaluate `E₀` under `Σ` without caching `E₀`
  (define (do-evl Σ E₀)
    (match E₀
      [(? -prim? p) (R-of p)]
      [(-•) (R-of (-● ∅))]
      [(-λ Xs E ℓ) (R-of E₀)]
      [(-case-λ cases ℓ)
       (define-values (Cases-rev ΔΣ*)
         (for/fold ([Cases-rev : (Listof Clo) '()] [ΔΣ : ΔΣ ⊥ΔΣ]) ([E (in-list cases)])
           (define-values (V ΔΣ*) (escape-clo Σ E))
           (values (cons V Cases-rev) (⧺ ΔΣ ΔΣ*))))
       (R-of (Case-Clo (reverse Cases-rev) ℓ) ΔΣ*)]
      [(-x x ℓ)
       (define-values (α modify-Vs)
         (cond [(symbol? x)
                (values (γ:lex x) (inst values V^))]
               [(equal? (ℓ-src ℓ) (-𝒾-src x))
                (values (γ:top x) (inst values V^))]
               [else
                (values (γ:wrp x)
                        (if (symbol? (-𝒾-src x))
                            (λ ([Vs : V^])
                              (for/set: : V^ ([V (in-set (unpack Vs Σ))])
                                (with-negative-party (ℓ-src ℓ) V)))
                            (λ ([Vs : V^])
                              (for/set: : V^ ([V (in-set (unpack Vs Σ))])
                                (with-positive-party 'dummy+
                                  (with-negative-party (ℓ-src ℓ) V))))))]))
       (define res (modify-Vs (lookup α Σ)))
       (when (∋ (unpack res Σ) -undefined)
         (err!  (Err:Undefined (if (-𝒾? x) (-𝒾-name x) x) ℓ)))
       (R-of (if (set? res) (set-remove res -undefined) res))]
      [(-@ f xs ℓ)
       (with-each-ans ([(ΔΣₕ Wₕ) (evl/arity Σ f 1 ℓ)])
         (define V^ₕ (car Wₕ))
         (with-collapsed/R [(cons Wₓ ΔΣₓ) (evl*/collapse (evl/single/collapse ℓ) (⧺ Σ ΔΣₕ) xs)]
           (ΔΣ⧺R (⧺ ΔΣₕ ΔΣₓ) (app (⧺ Σ ΔΣₕ ΔΣₓ) ℓ V^ₕ Wₓ))))]
      [(-if E E₁ E₂ ℓ)
       (with-each-path [(ΔΣs W) (evl/arity Σ E 1 ℓ)]
         (for/ans ([ΔΣ : ΔΣ (in-set ΔΣs)])
           (define Σ* (⧺ Σ ΔΣ))
           (with-split-Σ Σ* 'values W
             (λ (_ ΔΣ₁) (ΔΣ⧺R (⧺ ΔΣ ΔΣ₁) (evl (⧺ Σ* ΔΣ₁) E₁)))
             (λ (_ ΔΣ₂) (ΔΣ⧺R (⧺ ΔΣ ΔΣ₂) (evl (⧺ Σ* ΔΣ₂) E₂))))))]
      [(-wcm k v e) (error 'TODO "with-current-continuation-mark")]
      [(-begin Es)
       (match Es
         ['() (R-of -void)] ; unreachable if `begin` is in expr position
         [_
          (match-define-values (Es₀ (list Eₙ)) (split-at Es (sub1 (length Es))))
          (with-collapsed/R [ΔΣ₀ (evl*/discard/collapse evl/discard/collapse Σ Es₀)]
            (ΔΣ⧺R ΔΣ₀ (evl (⧺ Σ ΔΣ₀) Eₙ)))])]
      [(-begin0 E Es)
       (define r₀ (evl Σ E))
       (match (collapse-R/ΔΣ r₀)
         [(? values ΔΣ₀)
          (with-collapsed/R [ΔΣ* (evl*/discard/collapse evl/discard/collapse (⧺ Σ ΔΣ₀) Es)]
            (R⧺ΔΣ r₀ ΔΣ*))]
         [#f ⊥R])]
      [(-quote b) (if (Base? b) (R-of (-b b)) (error 'TODO "(quote ~a)" b))]
      [(-let-values bnds E ℓ)
       (define ΔΣₓs (evl-bnd* Σ ℓ bnds))
       (if (set-empty? ΔΣₓs)
           ⊥R
           (let ([r* (for/fold ([r : R ⊥R]) ([ΔΣₓ : ΔΣ (in-set ΔΣₓs)])
                       (R⊔ r (ΔΣ⧺R ΔΣₓ (evl (⧺ Σ ΔΣₓ) E))))])
             (fix-return (make-erasure bnds) Σ (R-escape-clos Σ r*))))]
      [(-letrec-values bnds E ℓ)
       (define ΔΣ₀
         (for*/fold ([ΔΣ₀ : ΔΣ ⊥ΔΣ])
                    ([bnd (in-list bnds)]
                     [x (in-list (Binding-lhs bnd))])
           (⧺ ΔΣ₀ (alloc-lex x {set -undefined}))))
       (define r*
         (with-collapsed/R [ΔΣₓ (evl*/discard/collapse (evl-set-bnd ℓ) (⧺ Σ ΔΣ₀) bnds)]
           (define ΔΣ* (⧺ ΔΣ₀ ΔΣₓ))
           (ΔΣ⧺R ΔΣ* (evl (⧺ Σ ΔΣ*) E))))
       (fix-return (make-erasure bnds) Σ (R-escape-clos Σ r*))]
      [(-set! X E ℓ)
       (with-collapsing/R [(ΔΣ:rhs rhs) (evl/arity Σ E 1 ℓ)]
         (define α (if (symbol? X) (γ:lex X) (γ:top X)))
         (define rhs^ (car (collapse-W^ rhs)))
         (define ΔΣ:mut
           (let ([muts (set-map (Σ@ α Σ)
                                (match-lambda
                                  [(and α (α:dyn (β:mut (== X)) _)) (mut α rhs^ Σ)]))])
             (foldl ΔΣ⊔ (car muts) (cdr muts))))
         (R-of -void (⧺ ΔΣ:rhs ΔΣ:mut)))]
      [(-error s ℓ) (err! (Err:Raised s ℓ)) ⊥R]
      [(-μ/c x E)
       (define α (α:dyn (β:x/c x) H₀))
       (define C:rec {set (X/C α)})
       (define ΔΣ₀ (alloc (γ:lex x) C:rec))
       (with-collapsed/R [(cons C ΔΣ₁) ((evl/single/collapse +ℓ₀) (⧺ Σ ΔΣ₀) E)]
         (R-of C:rec (⧺ ΔΣ₀ ΔΣ₁ (alloc α C))))]
      [(-->i (-var doms ?doms:rst) rngs)
       (: mk-Dom : -dom (U Clo V^) → (Values Dom ΔΣ))
       (define (mk-Dom dom C)
         (match-define (-dom x _ _ ℓ) dom)
         (cond [(Clo? C) (values (Dom x C ℓ) ⊥ΔΣ)]
               [else (define α (α:dyn (β:dom ℓ) H₀))
                     (values (Dom x α ℓ) (alloc α (unpack C Σ)))]))
       (: mk-Doms : (Listof -dom) (Listof (U V^ Clo)) → (Values (Listof Dom) ΔΣ))
       (define (mk-Doms doms Cs)
         (define-values (Doms:rev ΔΣ*)
           (for/fold ([Doms:rev : (Listof Dom) '()] [ΔΣ : ΔΣ ⊥ΔΣ])
                     ([domᵢ (in-list doms)] [Cᵢ (in-list Cs)])
             (define-values (Dom ΔΣ-dom) (mk-Dom domᵢ Cᵢ))
             (values (cons Dom Doms:rev) (⧺ ΔΣ ΔΣ-dom))))
         (values (reverse Doms:rev) ΔΣ*))

       (define (with-inits [Inits : (Listof Dom)] [ΔΣ-acc : ΔΣ])
         (if ?doms:rst
             (with-collapsed/R [(cons C ΔΣ₀) (evl-dom (⧺ Σ ΔΣ-acc) ?doms:rst)]
               (define-values (Rst ΔΣ₁) (mk-Dom ?doms:rst C))
               (with-doms (-var Inits Rst) (⧺ ΔΣ-acc ΔΣ₀ ΔΣ₁)))
             (with-doms (-var Inits #f) ΔΣ-acc)))

       (define (with-doms [doms : (-var Dom)] [ΔΣ-acc : ΔΣ])
         (if rngs
             (with-collapsed/R [(cons W-rngs ΔΣ₀)
                                (evl*/collapse evl-dom (⧺ Σ ΔΣ-acc) rngs)]
               (define-values (Rngs ΔΣ₁) (mk-Doms rngs W-rngs))
               (R-of (==>i doms Rngs) (⧺ ΔΣ-acc ΔΣ₀ ΔΣ₁)))
             (R-of (==>i doms #f) ΔΣ-acc)))
       
       (with-collapsed/R [(cons W-init ΔΣ₀) (evl*/collapse evl-dom Σ doms)]
         (define-values (Inits ΔΣ₁) (mk-Doms doms W-init))
         (with-inits Inits (⧺ ΔΣ₀ ΔΣ₁)))]
      [(case--> cases)
       (define-values (Cases ΔΣ) (evl/special Σ cases ==>i?))
       (R-of (Case-=> Cases) ΔΣ)]
      [(-∀/c xs E ℓ)
       (R-of (∀/C xs E H₀ ℓ) (escape ℓ (fv E₀) Σ))]))

  (: escape-clo : Σ -λ → (Values Clo ΔΣ))
  (define (escape-clo Σ E₀)
    (match-define (-λ Xs E ℓ) E₀)
    (values (Clo Xs E H₀ ℓ) (escape ℓ (fv E₀) Σ)))

  (: V^-escape-clos : Σ V^ → (Values V^ ΔΣ))
  (define (V^-escape-clos Σ Vs)
    (for/fold ([Vs : V^ Vs] [ΔΣ : ΔΣ ⊥ΔΣ]) ([V (in-set Vs)] #:when (-λ? V))
      (define-values (V* ΔΣ*) (escape-clo Σ V))
      (values (set-add (set-remove Vs V) V*) (⧺ ΔΣ ΔΣ*))))

  (: escape-clos : Σ W → (Values W ΔΣ))
  (define (escape-clos Σ W)
    (define ΔΣ* : ΔΣ ⊥ΔΣ)
    (define W* (map (λ ([Vs : V^]) (let-values ([(Vs* ΔΣ) (V^-escape-clos Σ Vs)])
                                     (set! ΔΣ* (⧺ ΔΣ* ΔΣ))
                                     Vs*))
                    W))
    (values W* ΔΣ*))

  (: R-escape-clos : Σ R → R)
  (define (R-escape-clos Σ₀ r)

    (: S-escape-clos : Σ S → (Values S ΔΣ))
    (define (S-escape-clos Σ S)
      (if (vector? S)
          (let ([ΔΣ : ΔΣ ⊥ΔΣ])
            (define S* (vector-map (λ ([Vs : V^])
                                     (let-values ([(Vs* ΔΣ*) (V^-escape-clos Σ Vs)])
                                       (set! ΔΣ (⧺ ΔΣ ΔΣ*))
                                       Vs*))
                                   S))
            (values S* ΔΣ))
          (V^-escape-clos Σ S)))

    (: ΔΣ-escape-clos : Σ ΔΣ → ΔΣ)
    (define (ΔΣ-escape-clos Σ ΔΣ₀)
      (for/fold ([acc : ΔΣ ⊥ΔΣ]) ([(α r) (in-hash ΔΣ₀)])
        (match-define (cons Vs N) r)
        (define-values (Vs* ΔΣ*) (S-escape-clos Σ Vs))
        (⧺ (hash-set acc α (cons Vs* N)) ΔΣ*)))

    (for*/fold ([acc : R ⊥R]) ([(W ΔΣs) (in-hash r)] [ΔΣᵢ : ΔΣ (in-set ΔΣs)])
      (define Σ* (⧺ Σ₀ ΔΣᵢ))
      (define-values (W* ΔΣ*) (escape-clos Σ* W))
      (R⊔ acc (R-of W* (⧺ ΔΣ* (ΔΣ-escape-clos Σ* ΔΣᵢ))))))

  (: make-erasure : (Listof Binding) → Renamings)
  (define (make-erasure bnds)
    (for*/hash : Renamings ([bnd (in-list bnds)] [x (in-list (car bnd))])
      (values (γ:lex x) #f)))

  (: evl-bnd* : Σ ℓ (Listof Binding) → (℘ ΔΣ))
  (define (evl-bnd* Σ₀ ℓ bnds)
    (define (evl-bnd [Σ : Σ] [bnd : Binding])
      (match-define (mk-Binding xs E) bnd)
      (define r (evl/arity Σ E (length xs) ℓ))
      (for/set: : (℘ ΔΣ) ([(rhs ΔΣs) (in-hash r)])
        (⧺ (collapse-ΔΣs ΔΣs) (alloc-lex* xs rhs))))

    (let step ([Σ : Σ Σ₀] [bnds : (Listof Binding) bnds])
      (match bnds
        ['() {set ⊥ΔΣ}]
        [(cons bnd₀ bnds*)
         (define ΔΣ₀s (evl-bnd Σ bnd₀))
         (for/fold ([ΔΣs* : (℘ ΔΣ) ∅]) ([ΔΣ₀ : ΔΣ (in-set ΔΣ₀s)])
           (define ΔΣ₁s (step (⧺ Σ ΔΣ₀) bnds*))
           (∪ (for/set: : (℘ ΔΣ) ([ΔΣ₁ : ΔΣ (in-set ΔΣ₁s)])
                (⧺ ΔΣ₀ ΔΣ₁))
              ΔΣs*))])))

  (: evl-set-bnd : ℓ → Σ Binding → (Option ΔΣ))
  ;; Run let-rec binding where the addresses have already been allocated
  (define ((evl-set-bnd ℓ) Σ bnd)
    (match-define (mk-Binding xs E) bnd)
    (: mut-lex : Symbol V^ ΔΣ → ΔΣ)
    (define (mut-lex x V^ ΔΣ) (⧺ ΔΣ (mut (resolve-lex x) V^ Σ)))
    (with-collapsing [(ΔΣ rhs) (evl/arity Σ E (length xs) ℓ)]
      (foldl mut-lex ΔΣ xs (collapse-W^ rhs))))

  (: evl-dom : Σ -dom → (Option (Pairof (U Clo V^) ΔΣ)))
  (define (evl-dom Σ dom)
    (match-define (-dom _ ?deps c ℓ) dom)
    (if ?deps
        (let ([ΔΣ (escape ℓ (set-subtract (fv c) (list->seteq ?deps)) Σ)])
          (cons (Clo (-var ?deps #f) c H₀ ℓ) ΔΣ))
        ((evl/single/collapse ℓ) Σ c)))

  (: evl/arity : Σ E Natural ℓ → R)
  ;; Run expression with arity guard
  (define (evl/arity Σ E n ℓ)
    (define r (evl Σ E))
    (for/fold ([r* : R r]) ([W (in-hash-keys r)])
      (if (= n (length W))
          r*
          (begin
            (err! (Err:Values n E W ℓ))
            (hash-remove r* W)))))

  (: evl/discard/collapse : Σ E → (Option ΔΣ))
  ;; Run expression for collapsed side-effect
  (define (evl/discard/collapse Σ E) (collapse-R/ΔΣ (evl Σ E)))

  (: evl/single/collapse : ℓ → Σ E → (Option (Pairof V^ Σ)))
  (define ((evl/single/collapse ℓ) Σ E)
    (with-collapsing [(ΔΣ Ws) (evl/arity Σ E 1 ℓ)]
      (cons (car (collapse-W^ Ws)) ΔΣ)))

  (: evl/special (∀ (X) Σ (Listof E) (V → Boolean : X) → (Values (Listof X) ΔΣ)))
  (define (evl/special Σ Es p?)
    (define-values (Xs-rev ΔΣ*)
      (for/fold ([Xs-rev : (Listof X) '()] [ΔΣ : ΔΣ ⊥ΔΣ]) ([E (in-list Es)])
        (define rᵢ (evl Σ E))
        (match-define (list (cons Wᵢ ΔΣsᵢ)) (hash->list rᵢ))
        (values (cons (assert (set-first (car Wᵢ)) p?) Xs-rev) (⧺ ΔΣ (collapse-ΔΣs ΔΣsᵢ)))))
    (values (reverse Xs-rev) ΔΣ*))

  (: evl*/discard/collapse (∀ (X) (Σ X → (Option ΔΣ)) Σ (Listof X) → (Option ΔΣ)))
  ;; Run sequence for collapsed side-effects
  (define (evl*/discard/collapse f Σ₀ xs)
    (let loop ([acc-ΔΣ : ΔΣ ⊥ΔΣ] [Σ : Σ Σ₀] [xs xs])
      (match xs
        ['() acc-ΔΣ]
        [(cons x₁ xs*)
         (define ΔΣ₁ (f Σ x₁))
         (if ΔΣ₁
             (loop (⧺ acc-ΔΣ ΔΣ₁) (⧺ Σ ΔΣ₁) xs*)
             #f)]))) 

  (: evl*/collapse (∀ (X Y)
                      (Σ X → (Option (Pairof Y ΔΣ)))
                      Σ (Listof X) →
                      (Option (Pairof (Listof Y) ΔΣ))))
  (define (evl*/collapse ev Σ₀ xs)
    (let loop ([acc-ΔΣ : ΔΣ ⊥ΔΣ]
               [acc-rev-ys : (Listof Y) '()]
               [Σ : Σ Σ₀]
               [xs xs])
      (match xs
        ['() (cons (reverse acc-rev-ys) acc-ΔΣ)]
        [(cons x₁ xs*)
         (match (ev Σ x₁)
           [(cons y₁ ΔΣ₁) (loop (⧺ acc-ΔΣ ΔΣ₁) (cons y₁ acc-rev-ys) (⧺ Σ ΔΣ₁) xs*)]
           [#f #f])])))
  )
