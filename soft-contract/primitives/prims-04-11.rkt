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
         racket/set
         racket/flonum
         racket/fixnum
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide prims-04-11@)

(define-unit prims-04-11@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  (def-pred vector?)
  (def-prim/custom (make-vector ⟪ℋ⟫ ℒ Σ Γ Ws)

    (def-prim/custom (internal-make-vector ⟪ℋ⟫ ℒ Σ Γ Ws)
      #:domain ([Wₙ exact-nonnegative-integer?] [Wᵥ any/c])
      (define σ (-Σ-σ Σ))
      (match-define (-W¹ Vₙ sₙ) Wₙ)
      (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
      (define sₐ (?t@ 'make-vector sₙ sᵥ))
      ;; Heuristic: more concrete vector if length is available concretely
      (match sₙ
        [(-b (? exact-nonnegative-integer? n))
         (define ⟪α⟫s ; with side effect widening store
           (for/list : (Listof ⟪α⟫) ([i (in-range n)])
             (define ⟪α⟫ (-α->⟪α⟫ (-α.idx ℒ ⟪ℋ⟫ (assert i index?))))
             (σ⊕! Σ Γ ⟪α⟫ Wᵥ)
             ⟪α⟫))
         {set (-ΓA (-Γ-facts Γ) (-W (list (-Vector ⟪α⟫s)) sₐ))}]
        [_
         (define ⟪α⟫ (-α->⟪α⟫ (-α.vct ℒ ⟪ℋ⟫)))
         (σ⊕! Σ Γ ⟪α⟫ Wᵥ) ; initializing, not mutating
         {set (-ΓA (-Γ-facts Γ) (-W (list (-Vector^ ⟪α⟫ Vₙ)) sₐ))}]))

    (define Ws*
      (match Ws
        [(list Wₙ) (list Wₙ -zero.W¹)]
        [_ Ws]))
    (.internal-make-vector ⟪ℋ⟫ ℒ Σ Γ Ws*))
  (def-prim/custom (vector ⟪ℋ⟫ ℒ Σ Γ Ws)
    (define σ (-Σ-σ Σ))
    (define sₐ (apply ?t@ 'vector (map -W¹-t Ws)))
    (define ⟪α⟫s ; with side effect widening store
      (for/list : (Listof ⟪α⟫) ([W (in-list Ws)] [i (in-naturals)])
        (define ⟪α⟫ (-α->⟪α⟫ (-α.idx ℒ ⟪ℋ⟫ (assert i index?))))
        (σ⊕! Σ Γ ⟪α⟫ W)
        ⟪α⟫))
    {set (-ΓA (-Γ-facts Γ) (-W (list (-Vector ⟪α⟫s)) sₐ))})
  (def-prim/todo vector-immutable
    (() #:rest list? . ->* . (and/c vector? immutable?)))
  (def-prim/custom (vector-length ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W vector?])
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'vector-length s))
    (define A
      (match V
        [(-Vector ⟪α⟫s) (list (-b (length ⟪α⟫s)))]
        [(-Vector^ _ n) (list n)]
        [(-Vector/guard (-Vector/C ⟪α⟫s) _ _) (list (-b (length ⟪α⟫s)))]
        [_ -Nat.Vs]))
    {set (-ΓA (-Γ-facts Γ) (-W A sₐ))})
  #;(def-prim/todo vector-ref
      (vector? exact-nonnegative-integer? . -> . any/c))
  #;(def-prim/todo vector-set!
      ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
  (def-prim vector->list (vector? . -> . list?)) ; FIXME retain content
  (def-prim/custom (list->vector ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W list?])
    (match-define (-Σ σ _ _) Σ)
    (match-define (-W¹ Vₗ sₗ) W)
    (define Vₐ
      (match Vₗ
        ;; Collect content of non-empty list
        [(? -St? Vₗ)
         (define α (-α->⟪α⟫ (-α.vct ℒ ⟪ℋ⟫)))
         (for ([V (in-set (extract-list-content σ Vₗ))])
           (σ⊕V! Σ α V))
         (-Vector^ α -PosNat.V)]
        ;; Empty list -> Empty vector
        [(-b (list))
         -Vector₀]
        ;; Default
        [_ (-● {set 'vector?})]))
    {set (-ΓA (-Γ-facts Γ) (-W (list Vₐ) (?t@ 'vector->list sₗ)))})
  (def-prim/todo vector->immutable-vector
    (vector? . -> . (and/c vector? immutable?)))
  (def-prim/todo vector-fill!
    ((and/c vector? (not/c immutable?)) any/c . -> . void?))
  (def-prim/todo vector-copy! ; FIXME uses
    ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?))
  #;[vector->values ; FIXME uses, var-values, `any` instead of `any/c`
     (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any)]

  ;; 4.11.1 Additional Vector Functions
  (def-prim/todo vector-set*! ; FIXME uses
    ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
  (def-prim/todo vector-map ; FIXME uses
    (procedure? vector? . -> . vector?))
  (def-prim/todo vector-map! ; FIXME uses
    (procedure? (and/c vector? (not/c immutable?)) . -> . vector?))
  #;[vector-append ; FIXME listof
     (() #:rest (listof vector?) . ->* . vector?)]
  (def-prim/todo vector-take
    (vector? exact-nonnegative-integer? . -> . vector?))
  (def-prim/todo vector-take-right
    (vector? exact-nonnegative-integer? . -> . vector?))
  (def-prim/todo vector-drop
    (vector? exact-nonnegative-integer? . -> . vector?))
  (def-prim/todo vector-drop-right
    (vector? exact-nonnegative-integer? . -> . vector?))
  (def-prim/todo vector-split-at
    (vector? exact-nonnegative-integer? . -> . (values vector? vector?)))
  (def-prim/todo vector-split-at-right
    (vector? exact-nonnegative-integer? . -> . (values vector? vector?)))
  (def-prim/todo vector-copy ; FIXME uses
    (vector? . -> . vector?))
  ; [HO] vector-filter vector-filter-not
  (def-prim/todo vector-count ; FIXME varargs
    (procedure? vector? . -> . exact-nonnegative-integer?))
  ; [HO] vector-argmin vector-argmax
  (def-prims (vector-member vector-memv vector-memq)
    (any/c vector? . -> . (or/c exact-nonnegative-integer? not)))
  )
