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

  ;; TODO: obsolete. Can be expressed directly in big step
  #;(define ℓ:mon (loc->ℓ (loc 'scv:mon 0 0 '())))
  #;(def (scv:mon Σ ℓ W)
    #:init ([src symbol?] [C contract?] [V any/c])
    (match src
      [(or {singleton-set (-b (and (? symbol?) (app symbol->string l)))}
           (-b (and (? symbol?) (app symbol->string l))))
       #:when l
       (define ctx (Ctx l (string->symbol (format "user-of-~a" l)) ℓ:mon ℓ))
       (mon Σ ctx C V)]
      [_ (error 'scv:mon "internal error")]))

  ;; TODO: obsolete. Can be expressed directly in big step
  (def (scv:struct/c Σ ℓ W)
    #:init ([Vₖ any/c])
    #:rest [Wᵣ (listof contract?)]
    ((inst fold-ans V)
     (match-lambda
       [(-st-mk 𝒾)
        (if (= (count-struct-fields 𝒾) (length Wᵣ))
            (let-values ([(αs ΔΣ) (alloc-each Wᵣ (λ (i) (β:st/c 𝒾 ℓ i)))])
              (just (St/C 𝒾 αs ℓ) ΔΣ))
            (err (Err:Arity (-𝒾-name 𝒾) Wᵣ ℓ)))]
       [_ (err (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'constructor?}) (list Vₖ)))])
     (unpack Vₖ Σ)))

  (def (scv:hash-key Σ ℓ W)
    #:init ([Vₕ hash?])
    (define ac₁ : (V → (Values R (℘ Err)))
      (match-lambda
        [(Empty-Hash) (err (Blm (ℓ-src ℓ) ℓ (ℓ-with-src ℓ 'hash-ref)
                                (list {set (Not/C (γ:imm 'hash-empty?) +ℓ₀)})
                                (list {set (Empty-Hash)})))]
        [(Hash-Of αₖ _) (just (Σ@ αₖ Σ))]
        [(Guarded ctx (Hash/C αₖ _ _) α)
         (with-collapsing/R [(ΔΣ Ws) (app Σ ℓ {set 'scv:hash-key} (list (Σ@ α Σ)))]
           (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (Σ@ αₖ Σ) (car (collapse-W^ Ws)))))]
        [(? -●?) (just (-● ∅))]
        [(? α? α) (fold-ans ac₁ (Σ@ α Σ))]
        [_ !!!]))
    (fold-ans ac₁ Vₕ))

  (def (scv:hash-val Σ ℓ W)
    #:init ([Vₕ hash?])
    (define ac₁ : (V → (Values R (℘ Err)))
      (match-lambda
        [(Empty-Hash) (err (Blm (ℓ-src ℓ) ℓ (ℓ-with-src ℓ 'hash-ref)
                                (list {set (Not/C (γ:imm 'hash-empty?) +ℓ₀)})
                                (list {set (Empty-Hash)})))]
        [(Hash-Of _ αᵥ) (just (Σ@ αᵥ Σ))]
        [(Guarded ctx (Hash/C _ αᵥ _) α)
         (with-collapsing/R [(ΔΣ Ws) (app Σ ℓ {set 'scv:hash-val} (list (Σ@ α Σ)))]
           (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (Σ@ αᵥ Σ) (car (collapse-W^ Ws)))))]
        [(? -●?) (just (-● ∅))]
        [(? α? α) (fold-ans ac₁ (Σ@ α Σ))]
        [_ !!!]))
    (fold-ans ac₁ Vₕ))

  ;; HACK for some internal uses of `make-sequence`
  (def (make-sequence Σ ℓ W)
    #:init ()
    #:rest [_ (listof any/c)]
    (just (list {set -car} {set -cdr} {set 'values} {set -one} {set -cons?} {set -ff} {set -ff})))
  )
