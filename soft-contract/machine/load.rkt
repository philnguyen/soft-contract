#lang typed/racket/base

(provide 𝑰)

(require
 racket/match racket/list
 "../utils/map.rkt" "../utils/set.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/addr.rkt" "../runtime/val.rkt" "../runtime/env.rkt" "../runtime/path-inv.rkt"
 "../runtime/store.rkt" "../runtime/summ.rkt"
 "definition.rkt" "havoc.rkt")

(: 𝑰 : (Listof -module) (Listof -module-level-form) → (Values -ς -e))
;; Load program to intial machine state
(define (𝑰 ms init-prim)

  ;; Generate havoc function and top-level expression
  (define-values (havoc e_hv) (gen-havoc ms))

  ;; Allocate primitives in initial heap
  (define σ₀
    (for/fold ([σ : -σ (⊔ -σ⊥ (-α.def -havoc-id) havoc)])
              ([form init-prim])
      (match form
        ;; general top-level form
        [(? -e?) σ]
        [(-define-values _ ids e)
         (match ids
           [(list id)
            (define-values (σ* V _) (alloc-e σ e))
            (⊔ σ* (-α.def (-id id 'Λ)) V)]
           [else
            (error '𝑰 "TODO: general top-level. For now can't handle `define-~a-values`"
                   (length ids))])]
        [(? -require?) σ]
        ;; provide
        [(-provide _ specs)
         (for/fold ([σ : -σ σ]) ([spec specs])
           (match-define (-p/c-item x c) spec)
           (define-values (σ₁ C _) (alloc-e σ c))
           (define id (-id x 'Λ))
           (define σ₂ (⊔ σ₁ (-α.ctc id) C))
           (cond
             [(hash-has-key? σ₂ (-α.def id)) σ₂]
             [else (⊔ σ₂ (-α.def id) -●/V)]))]
        ;; submodule-form
        [(? -module?) (error '𝑰 "TODO: sub-module forms")])))

  (define top-exps
    (append-map
     (λ ([m : -module]) : (Listof (U -define-values -provide))
       (for/list ([e (-plain-module-begin-body (-module-body m))]
                  #:when (or (-define-values? e) (-provide? e)))
         e))
     ms))

  (define τ₀ (-τ e_hv -ρ⊥ -Γ⊤))
  (define Ξ₀ : -Ξ (hash τ₀ ∅))
  
  (define-values (E₀ κ₀)
    (match top-exps
      ['() (values (-↓ e_hv -ρ⊥) τ₀)]
      [(cons e† exps)
       (values e† (-kont (-φ.top exps e_hv) τ₀))]))

  (values (-ς E₀ -Γ⊤ κ₀ σ₀ Ξ₀ -M⊥) e_hv))

(: alloc-e : -σ -e → (Values -σ -V -e))
(define (alloc-e σ e)
  
  (define (error-ambig)
    (error 'alloc-e "ambiguity when checking for flat contract"))
  
  (match e
    [(? -v? v) (values σ (close-Γ -Γ⊤ (close e -ρ⊥)) v)]
    [(-ref (-id o 'Λ) _ _) (values σ (prim-name->unsafe-prim o) (prim-name->unsafe-prim o))]
    [(-->i doms rst rng pos)
     (define-values (σ* xs-rev γs-rev cs-rev)
       (for/fold ([σ : -σ σ]
                  [xs-rev : (Listof Symbol) '()]
                  [γs-rev : (Listof -α.dom) '()]
                  [es-rev : (Listof -e) '()])
                 ([dom : (Pairof Symbol -e) doms])
         (match-define (cons x c) dom)
         (define-values (σi Vi vi) (alloc-e σ c))
         (define γ (-α.dom vi))
         (values (⊔ σi γ Vi) (cons x xs-rev) (cons γ γs-rev) (cons vi es-rev))))
     (define xs (reverse xs-rev))
     (define cs (reverse xs-rev))
     (define γs (reverse γs-rev))
     (define Doms (map (inst cons Symbol -α.dom) xs γs))
     (define dom↓s (map (inst cons Symbol -e) xs cs))
     
     (match rst
       [(cons x c)
        (define-values (σ** C-rst c-rst) (alloc-e σ* c))
        (define γ-rst (-α.rst c-rst))
        (values (⊔ σ** γ-rst C-rst)
                (-=>i Doms (cons x γ-rst) rng -ρ⊥ -Γ⊤)
                (-->i dom↓s (cons x c-rst) rng 0))]
       [#f
        (values σ*
                (-=>i Doms #f rng -ρ⊥ -Γ⊤)
                (-->i dom↓s #f rng 0))])]
    [(-@ (and k (-st-mk si)) es pos)
     (define-values (σ* γs vs) (alloc-es σ es -α.fld))
     (values σ*
             (-St si (cast γs (Listof -α.fld)))
             (-@ k vs -Λ))]
    [(-@ (or 'and/c (-ref (-id 'and/c 'Λ) _ _)) (list c₁ c₂) l)
     (define-values (σ₁ V₁ v₁) (alloc-e σ  c₁))
     (define γ₁ (-α.and/c-l v₁))
     (define-values (σ₂ V₂ v₂) (alloc-e (⊔ σ₁ γ₁ V₁) c₂))
     (define γ₂ (-α.and/c-r v₂))
     (define flat? (and (C-flat? V₁) (C-flat? V₂)))
     (values (⊔ σ₂ γ₂ V₂) (-And/C flat? γ₁ γ₂) (-@ 'and/c (list v₁ v₂) -Λ))]
    [(-@ (or 'or/c (-ref (-id 'or/c 'Λ) _ _)) (list c₁ c₂) l)
     (define-values (σ₁ V₁ v₁) (alloc-e σ  c₁))
     (define γ₁ (-α.or/c-l v₁))
     (define-values (σ₂ V₂ v₂) (alloc-e (⊔ σ₁ γ₁ V₁) c₂))
     (define γ₂ (-α.or/c-r v₂))
     (define flat? (and (C-flat? V₁) (C-flat? V₂)))
     (values (⊔ σ₂ γ₂ V₂) (-Or/C flat? γ₁ γ₂) (-@ 'or/c (list v₁ v₂) -Λ))]
    [(-@ (or 'not/c (-ref (-id 'not/c 'Λ) _ _)) (list c) l)
     (define-values (σ* V v) (alloc-e σ c))
     (define γ (-α.not/c v))
     (values (⊔ σ* γ V) (-Not/C γ) (-@ 'not/c (list v) -Λ))]
    [(-@ (or 'vectorof (-ref (-id 'vectorof 'Λ) _ _)) (list c) _)
     (define-values (σ* V v) (alloc-e σ c))
     (define α (-α.vectorof v))
     (values (⊔ σ* α V) (-Vectorof α) (-@ 'vectorof (list v) -Λ))]
    [(-@ (or 'vector/c (-ref (-id 'vector/c 'Λ) _ _)) cs _)
     (define-values (σ* γs vs) (alloc-es σ cs -α.vector/c))
     (values σ*
             (-Vector/C (cast γs (Listof -α.vector/c)))
             (-@ 'vector/c vs -Λ))]
    [(-struct/c s cs pos)
     (define id (-struct-info-id s))
     (define-values (σ* αs-rev flat? vs-rev)
       (for/fold ([σ* : -σ σ]
                  [αs-rev : (Listof -α.struct/c) '()]
                  [flat? : Boolean #t]
                  [vs-rev : (Listof -e) '()])
                 ([(c i) (in-indexed cs)])
         (define-values (σ_i V v) (alloc-e σ* c))
         (define α (-α.struct/c v))
         (values (⊔ σ_i α V) (cons α αs-rev) (and flat? (C-flat? V)) (cons v vs-rev))))
     (values σ* (-St/C flat? s (reverse αs-rev)) (-struct/c s (reverse vs-rev) 0))]
    [e (error '𝑰 "TODO: execute general expression. For now can't handle ~a"
              (show-e e))]))

(: alloc-es : -σ (Listof -e) (-e → -α) → (Values -σ (Listof -α) (Listof -e)))
(define (alloc-es σ es mk-α)
  (define-values (σ* αs-rev es-rev)
    (for/fold ([σ : -σ σ] [αs-rev : (Listof -α) '()] [es-rev : (Listof -e) '()])
              ([e es])
      (define-values (σ* V v) (alloc-e σ e))
      (define α (mk-α v))
      (values (⊔ σ* α V) (cons α αs-rev) (cons v es-rev))))
  (values σ* (reverse αs-rev) (reverse es-rev)))
