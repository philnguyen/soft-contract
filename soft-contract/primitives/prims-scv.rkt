#lang typed/racket/base

(provide prims-scv@)

(require racket/match
         racket/contract
         typed/racket/unit
         racket/set
         unreachable
         set-extras
         "../utils/debug.rkt"
         "../utils/list.rkt"
         "../utils/patterns.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-scv@
  (import static-info^
          prim-runtime^
          sto^ val^ cache^
          app^ mon^ exec^
          prover^)
  (export)

  (def (scv:mon Σ ℓ W)
    #:init ([src symbol?] [C contract?] [V any/c])
    (match src
      [(or {singleton-set (-b (? symbol? name))})
       (define l (current-module))
       (define ctx (Ctx l #|TODO|# l ℓ ℓ))
       (mon Σ ctx C V)]
      [_ (error 'scv:mon "internal error")]))

  ;; TODO: obsolete. Can be expressed directly in big step
  (def (scv:struct/c Σ ℓ W)
    #:init ([Vₖ any/c])
    #:rest [Wᵣ (listof contract?)]
    (define-set seen : α #:mutable? #t)
    (define step : (V → (Values R (℘ Err)))
      (match-lambda
        [(-st-mk 𝒾)
         (if (= (count-struct-fields 𝒾) (length Wᵣ))
             (let ([α (α:dyn (β:st/c-elems ℓ 𝒾) H₀)])
               (just (St/C α) (alloc α (list->vector Wᵣ))))
             (err (Err:Arity (-𝒾-name 𝒾) Wᵣ ℓ)))]
        [(Guarded _ _ α)
         (cond [(seen-has? α) (values ⊥R ∅)]
               [else (seen-add! α)
                     (fold-ans step (unpack α Σ))])]
        [_ (err (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'constructor?}) (list Vₖ)))]))
    (fold-ans step (unpack Vₖ Σ)))

  (def (scv:hash-key Σ ℓ W)
    #:init ([Vₕ hash?])
    (define ac₁ : (V → (Values R (℘ Err)))
      (match-lambda
        [(Empty-Hash) (err (Blm (ℓ-src ℓ) ℓ (ℓ-with-src ℓ 'hash-ref)
                                (list {set (Not/C (γ:imm 'hash-empty?) +ℓ₀)})
                                (list {set (Empty-Hash)})))]
        [(Hash-Of αₖ _) (just (Σ@ αₖ Σ))]
        [(Guarded (cons l+ l-) (Hash/C αₖ _ ℓₕ) α)
         (define ctx (Ctx l+ l- ℓₕ ℓ))
         (with-collapsing/R [(ΔΣ Ws) (app Σ ℓₕ {set 'scv:hash-key} (list (Σ@ α Σ)))]
           (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (Σ@ αₖ Σ) (car (collapse-W^ Ws)))))]
        [(? -●?) (just (-● ∅))]
        [(? α? α) (fold-ans ac₁ (Σ@ α Σ))]
        [_ !!!]))
    (fold-ans/collapsing ac₁ Vₕ))

  (def (scv:hash-val Σ ℓ W)
    #:init ([Vₕ hash?])
    (define ac₁ : (V → (Values R (℘ Err)))
      (match-lambda
        [(Empty-Hash) (err (Blm (ℓ-src ℓ) ℓ (ℓ-with-src ℓ 'hash-ref)
                                (list {set (Not/C (γ:imm 'hash-empty?) +ℓ₀)})
                                (list {set (Empty-Hash)})))]
        [(Hash-Of _ αᵥ) (just (Σ@ αᵥ Σ))]
        [(Guarded (cons l+ l-) (Hash/C _ αᵥ ℓₕ) α)
         (define ctx (Ctx l+ l- ℓₕ ℓ))
         (with-collapsing/R [(ΔΣ Ws) (app Σ ℓₕ {set 'scv:hash-val} (list (Σ@ α Σ)))]
           (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (Σ@ αᵥ Σ) (car (collapse-W^ Ws)))))]
        [(? -●?) (just (-● ∅))]
        [(? α? α) (fold-ans ac₁ (Σ@ α Σ))]
        [_ !!!]))
    (fold-ans/collapsing ac₁ Vₕ))

  ;; HACK for some internal uses of `make-sequence`
  (def (make-sequence Σ ℓ W)
    #:init ()
    #:rest [_ (listof any/c)]
    (just (list {set -car} {set -cdr} {set 'values} {set -one} {set -cons?} {set -ff} {set -ff})))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; MISC
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-pred index?)
  )
