#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/flonum
         racket/fixnum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         "../utils/debug.rkt"
         "../utils/patterns.rkt"
         "../utils/function.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide prims-04-11@)

(define-unit prims-04-11@
  (import prim-runtime^
          evl^ val^ sto^
          prover^
          step^ approx^ mon^ app^)
  (export)
  
  (def-pred vector?)
  (splicing-let
      ([.internal-make-vector
        (let ()
          (def (internal-make-vector W ℓ Φ^ Ξ Σ)
            #:init ([Tₙ exact-nonnegative-integer?]
                    [Tᵥ any/c])
            (define H (Ξ:co-ctx Ξ))
            (match Tₙ
              [(singleton-set (-b (? exact-nonnegative-integer? n)))
               (define αs : (Listof α)
                 (for/list ([i (in-range n)])
                   (define α (mk-α (-α:idx ℓ H (assert i index?))))
                   (⊔T! Σ Φ^ α Tᵥ)
                   α))
               {set (ret! (T->R (Vect αs) Φ^) Ξ Σ)}]
              [_
               (define α (mk-α (-α:vct ℓ H)))
               (⊔T! Σ Φ^ α Tᵥ)
               {set (ret! (T->R (Vect^ α (T->V Σ Φ^ Tₙ)) Φ^) Ξ Σ)}]))
          .internal-make-vector)])
    (def (make-vector W ℓ Φ^ Ξ Σ)
      #:init ()
      #:rest [W (listof any/c)]
      (define W*
        (match W
          [(list Tₙ) (list Tₙ {set (-b 0)})]
          [_ W]))
      (.internal-make-vector W* ℓ Φ^ Ξ Σ)))
  
  (def (vector W ℓ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof any/c)]
    (define H (Ξ:co-ctx Ξ))
    (define αs : (Listof α) ; with side-effect allocating
      (for/list ([T (in-list W)] [i (in-naturals)])
        (define α (mk-α (-α:idx ℓ H (assert i index?))))
        (⊔T! Σ Φ^ α T)
        α))
    {set (ret! (T->R (Vect αs) Φ^) Ξ Σ)})
  (def vector-immutable
    (∀/c (α) (() #:rest (listof α) . ->* . (and/c (vectorof α) immutable?))))
  (def (vector-length W ℓ Φ^ Ξ Σ)
    #:init ([T vector?])
    {set (ret! (T->R (vec-len T) Φ^) Ξ Σ)})

  (def (vector-ref W ℓ Φ^ Ξ₀ Σ)
    #:init ([Tᵥ vector?] [Tᵢ integer?])
    (set-union-map
     (match-lambda
       [(Vect αs)
        (define Vₐ^
          (for/fold ([acc : V^ ∅])
                    ([α (in-list αs)]
                     [i : Natural (in-naturals)]
                     #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
            ((iter-⊔ V^⊔) acc (Σᵥ@ Σ α))))
        {set (ret! (T->R Vₐ^ Φ^) Ξ₀ Σ)}]
       [(Vect^ α n)
        {set (ret! (T->R (Σᵥ@ Σ α) Φ^) Ξ₀ Σ)}]
       [(X/G ctx G αᵥ)
        (define lo (Ctx-src ctx))
        (define Tᵥ* (Σᵥ@ Σ αᵥ))
        (match G
          [(Vect/C αℓs)
           (for/union : (℘ Ξ) ([αℓᵢ (in-list αℓs)]
                               [i : Natural (in-naturals)]
                               #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
             (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
             (define Ξ* (K+ (F:Mon:C (Ctx-with-ℓ ctx ℓᵢ) (Σᵥ@ Σ αᵢ)) Ξ₀))
             ((app₁ 'vector-ref) (list Tᵥ* Tᵢ) ℓ Φ^ Ξ* Σ))]
          [(Vectof αℓ*)
           (match-define (αℓ α* ℓ*) αℓ*)
           (define Ξ* (K+ (F:Mon:C (Ctx-with-ℓ ctx ℓ*) (Σᵥ@ Σ α*)) Ξ₀))
           ((app₁ 'vector-ref) (list Tᵥ* Tᵢ) ℓ Φ^ Ξ* Σ)])]
       [_ {set (ret! (T->R (-● ∅) Φ^) Ξ₀ Σ)}])
     (T->V Σ Φ^ Tᵥ)))
  
  (def (vector-set! W ℓ Φ^ Ξ₀ Σ)
    #:init ([Tᵥ^ vector?] [Tᵢ integer?] [Tᵤ any/c])
    (define-thunk/memo (done) : (℘ Ξ) {set (ret! (T->R {set -void} Φ^) Ξ₀ Σ)})
    (set-union-map
     (match-lambda
       [(Vect αs)
        (for ([α (in-list αs)]
              [i (in-naturals)] #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
          (⊔T! Σ Φ^ α Tᵤ))
        (done)]
       [(Vect^ α n) (⊔T! Σ Φ^ α Tᵤ) (done)]
       [(X/G ctx G αᵥ)
        (define ctx* (Ctx-flip ctx))
        (define Tᵥ*^ (Σᵥ@ Σ αᵥ))
        (match G
          [(Vect/C αℓs)
           (for/union : (℘ Ξ) ([(αℓᵢ i) (in-indexed αℓs)]
                               #:when (possbly? Σ (R (list Tᵢ (-b i)) Φ^) '=))
             (match-define (αℓ αᵢ ℓᵢ) αℓᵢ)
             (define Ξ* (K+ (F:Ap (list Tᵢ Tᵥ*^ 'vector-set!) '() ℓ) Ξ₀))
             (mon (Σᵥ@ Σ αᵢ) Tᵤ (Ctx-with-ℓ ctx* ℓᵢ) Φ^ Ξ* Σ))]
          [(Vectof αℓ*)
           (match-define (αℓ α* ℓ*) αℓ*)
           (define Ξ* (K+ (F:Ap (list Tᵢ Tᵥ*^ 'vector-set!) '() ℓ) Ξ₀))
           (mon (Σᵥ@ Σ α*) Tᵤ (Ctx-with-ℓ ctx* ℓ*) Φ^ Ξ* Σ)])]
       [_ (done)])
     (T->V Σ Φ^ Tᵥ^)))
  
  (def vector->list (∀/c (α) ((vectorof α) . -> . (listof α))))
  (def list->vector (∀/c (α) ((listof α) . -> . (vectorof α))))
  
  (def vector->immutable-vector (∀/c (α) ((vectorof α) . -> . (and/c (vectorof α) immutable?))))
  (def vector-fill! ((and/c vector? (not/c immutable?)) any/c . -> . void?))
  (def vector-copy!
    (case->
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?]
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? exact-nonnegative-integer? . -> . void?]
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . void?]))
  #;[vector->values ; FIXME uses, var-values, `any` instead of `any/c`
     (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any)]

  (def build-vector (∀/c (α) (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . α) . -> . (vectorof α))))

  ;; 4.11.1 Additional Vector Functions
  #;(def vector-set*! ; FIXME uses
    ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
  (def vector-map (∀/c (α β) ((α . -> . β) (vectorof α) . -> . (vectorof β)))) ; FIXME varargs
  (def vector-map! ; FIXME uses
    (∀/c (α β)
         ((α . -> . β)
          (and/c (not/c immutable?) (vectorof α)) . -> . (vectorof β))))
  (def vector-append
     (∀/c (α) (() #:rest (listof (vectorof α)) . ->* . (vectorof α))))
  (def* (vector-take vector-take-right vector-drop vector-drop-right)
    (∀/c (α) ((vectorof α) exact-nonnegative-integer? . -> . (vectorof α))))
  (def* (vector-split-at vector-split-at-right)
    (∀/c (α) ((vectorof α) exact-nonnegative-integer? . -> .
                           (values (vectorof α) (vectorof α)))))
  (def vector-copy
    (∀/c (α)
         (case->
          [(vectorof α) . -> . (vectorof α)]
          [(vectorof α) exact-nonnegative-integer? . -> . (vectorof α)]
          [(vectorof α) exact-nonnegative-integer? exact-nonnegative-integer? . -> . (vectorof α)])))
  (def* (vector-filter vector-filter-not)
    (∀/c (α _) ((α . -> . _) (vectorof α) . -> . (vectorof α))))
  (def vector-count ; FIXME varargs
    (∀/c (α _) ((α . -> . _) (vectorof α) . -> . exact-nonnegative-integer?)))
  (def* (vector-argmin vector-argmax) (∀/c (α) ((α . -> . real?) (vectorof α) . -> . α)))
  (def* (vector-member vector-memv vector-memq)
    (∀/c (_) (_ vector? . -> . (or/c exact-nonnegative-integer? not))))
  )
