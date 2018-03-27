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
          evl^ sto^
          prover^
          step^)
  (export)
  
  (def-pred vector?)
  (splicing-let
      ([.internal-make-vector
        (let ()
          (def (internal-make-vector W ℓ Φ^ Ξ Σ)
            #:init ([Vₙ exact-nonnegative-integer?]
                    [Vᵥ any/c])
            (define H (Ξ:co-ctx Ξ))
            (match Vₙ
              [(singleton-set (-b (? exact-nonnegative-integer? n)))
               (define αs : (Listof α)
                 (for/list ([i (in-range n)])
                   (define α (mk-α (-α:idx ℓ H (assert i index?))))
                   (⊔ᵥ! Σ α Vᵥ)
                   α))
               {set (ret! (V->R (Vect αs) Φ^) Ξ Σ)}]
              [_
               (define α (mk-α (-α:vct ℓ H)))
               (⊔ᵥ! Σ α Vᵥ)
               {set (ret! (V->R (Vect^ α Vₙ) Φ^) Ξ Σ)}]))
          .internal-make-vector)])
    (def (make-vector W ℓ Φ^ Ξ Σ)
      #:init ()
      #:rest [W (listof any/c)]
      (define W*
        (match W
          [(list Vₙ) (list Vₙ {set (-b 0)})]
          [_ W]))
      (.internal-make-vector W* ℓ Φ^ Ξ Σ)))
  
  (def (vector W ℓ Φ^ Ξ Σ)
    #:init ()
    #:rest [W (listof any/c)]
    (define H (Ξ:co-ctx Ξ))
    (define αs : (Listof α) ; with side-effect allocating
      (for/list ([V (in-list W)] [i (in-naturals)])
        (define α (mk-α (-α:idx ℓ H (assert i index?))))
        (⊔ᵥ! Σ α V)
        α))
    {set (ret! (V->R (Vect αs) Φ^) Ξ Σ)})
  (def vector-immutable
    (∀/c (α) (() #:rest (listof α) . ->* . (and/c (vectorof α) immutable?))))
  (def (vector-length W ℓ Φ^ Ξ Σ)
    #:init ([V vector?])
    {set (ret! (V->R (vec-len V) Φ^) Ξ Σ)})

  (def (vector-ref W ℓ Φ^ Ξ₀ Σ)
    #:init ([Vᵥ vector?] [Vᵢ integer?])
    (define with (inst with-2-paths Ξ))
    (with (λ () (split-results Σ (R (list Vᵥ) Φ^) 'vector? #:fast? #t))
      (λ (R^)
        ???)
      (λ (R^)
        (r:blm ℓ 'vector-ref '(vector?) (collapse-R^/W^ R^))))
    #;(for/union : (℘ Ξ) ([Vᵥ (in-set Vᵥ^)])
      (match Vᵥ
        [(Vect αs)
         (define Vₐ^
           (for/fold ([Vₐ^ : -V^ ∅])
                     ([α : ⟪α⟫ (in-list ⟪α⟫s)]
                      [i : Natural (in-naturals)]
                      #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
             (V⊕ φ Vₐ^ (σ@ Σ (-φ-cache φ) α))))
         (⟦k⟧ (list Vₐ^) H φ Σ)]
        [(-Vector^ α n)
         (⟦k⟧ (list (σ@ Σ (-φ-cache φ) α)) H φ Σ)]
        [(-Vector/guard grd αᵥ ctx)
         (define lo (-ctx-src ctx))
         (match grd
           [(-Vector/C ⟪α⟫ℓs)
            (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                                 [i : Natural (in-naturals)]
                                 #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
                       (match-define (-⟪α⟫ℓ αᵢ ℓᵢ) ⟪α⟫ℓ)
                       (define ⟦k⟧* (let ([Cᵢ^ (σ@ Σ (-φ-cache φ) αᵢ)])
                                      (mon.c∷ (ctx-with-ℓ ctx ℓᵢ) Cᵢ^ ⟦k⟧)))
                       (define Vᵥ^* (σ@ Σ (-φ-cache φ) αᵥ))
                       (.vector-ref ℓ (list Vᵥ^* Vᵢ) H φ Σ ⟦k⟧*))]
           [(-Vectorof ⟪α⟫ℓ)
            (match-define (-⟪α⟫ℓ α* ℓ*) ⟪α⟫ℓ)
            (define ⟦k⟧* (let ([C*^ (σ@ Σ (-φ-cache φ) α*)])
                           (mon.c∷ (ctx-with-ℓ ctx ℓ*) C*^ ⟦k⟧)))
            (define Vᵥ*^ (σ@ Σ (-φ-cache φ) αᵥ))
            (.vector-ref ℓ (list Vᵥ*^ Vᵢ) H φ Σ ⟦k⟧*)])]
        [_
         (⟦k⟧ (list {set (-● ∅)}) H φ Σ)])))
  
  #;(def (vector-set! ℓ Vs H φ Σ ⟦k⟧)
    #:init ([Vᵥ^ vector?] [Vᵢ integer?] [Vᵤ any/c])
    (for/union : (℘ -ς) ([Vᵥ (in-set Vᵥ^)])
      (match Vᵥ
        [(-Vector αs)
         (define φ*
           (for/fold ([φ : -φ φ])
                     ([α (in-list αs)]
                      [i : Natural (in-naturals)]
                      #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
             (mut! Σ φ α Vᵤ)))
         (⟦k⟧ (list {set -void}) H φ* Σ)]
        [(-Vector^ α n)
         (⟦k⟧ (list {set -void}) H (mut! Σ φ α Vᵤ) Σ)]
        [(-Vector/guard grd αᵥ ctx)
         (define ctx* (ctx-neg ctx))
         (define Vᵥ*^ (σ@ Σ (-φ-cache φ) αᵥ))
         (match grd
           [(-Vector/C ⟪α⟫ℓs)
            (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                                 [i : Natural (in-naturals)]
                                 #:when (plausible-index? (-Σ-σ Σ) φ Vᵢ i))
               (match-define (-⟪α⟫ℓ αᵢ ℓᵢ) ⟪α⟫ℓ)
               (define Cᵢ^ (σ@ Σ (-φ-cache φ) αᵢ))
               (define ⟦chk⟧ (mk-mon (ctx-with-ℓ ctx* ℓᵢ) (mk-A (list Cᵢ^)) (mk-A (list Vᵤ))))
               (⟦chk⟧ ⊥ρ H φ Σ (ap∷ (list Vᵢ Vᵥ*^ {set 'vector-set!}) '() ⊥ρ ℓ ⟦k⟧)))]
           [(-Vectorof ⟪α⟫ℓ)
            (match-define (-⟪α⟫ℓ α* ℓ*) ⟪α⟫ℓ)
            (define C*^ (σ@ Σ (-φ-cache φ) α*))
            (define ⟦chk⟧ (mk-mon (ctx-with-ℓ ctx* ℓ*) (mk-A (list C*^)) (mk-A (list Vᵤ))))
            (⟦chk⟧ ⊥ρ H φ Σ (ap∷ (list Vᵢ Vᵥ*^ {set 'vector-set!}) '() ⊥ρ ℓ ⟦k⟧))])]
        [_
         (⟦k⟧ (list {set -void}) H φ Σ)])))
  
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
