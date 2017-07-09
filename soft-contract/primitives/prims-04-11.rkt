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
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
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
  (import prim-runtime^ proof-system^ widening^ kont^ app^ compile^ val^ pc^ sto^ instr^ env^)
  (export)

  (def-pred vector?)
  (splicing-let
      ([.internal-make-vector
        (let ()
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
          .internal-make-vector)])
    (def-prim/custom (make-vector ⟪ℋ⟫ ℒ Σ Γ Ws)
      (define Ws*
        (match Ws
          [(list Wₙ) (list Wₙ (+W¹ -zero))]
          [_ Ws]))
      (.internal-make-vector ⟪ℋ⟫ ℒ Σ Γ Ws*)))
  
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
        [_ (list (+● 'exact-nonnegative-integer?))]))
    {set (-ΓA (-Γ-facts Γ) (-W A sₐ))})

  (def-ext (vector-ref ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ vector?] [Wᵢ integer?])
    (match-define (-Σ σ _) Σ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (define sₐ (?t@ 'vector-ref sᵥ sᵢ))
    (match Vᵥ
      [(-Vector ⟪α⟫s)
       #;(hash-ref cache (cons Wᵥ Wᵢ)
                   (λ ()
                     (printf "ref ~a ~a:~n" (show-W¹ Wᵥ) (show-W¹ Wᵢ))
                     (for ([⟪α⟫ : ⟪α⟫ (in-list ⟪α⟫s)]
                           [i : Natural (in-naturals)]
                           #:when (plausible-index? σ Γ Wᵢ i))
                       (printf "  - ~a ↦ ~a~n" i (set-count (σ@ σ ⟪α⟫))))
                     (printf "~n")))
       (for/union : (℘ -ς) ([⟪α⟫ : ⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (for/union : (℘ -ς) ([V (in-set (σ@ σ ⟪α⟫))])
                             (⟦k⟧ (-W (list V) sₐ) Γ* ⟪ℋ⟫ Σ)))]
      [(-Vector^ α n)
       (for/union : (℘ -ς) ([V (σ@ σ α)])
                  (⟦k⟧ (-W (list V) sₐ) Γ ⟪ℋ⟫ Σ))]
      [(-Vector/guard grd ⟪α⟫ᵥ l³)
       (match-define (-l³ _ _ lo) l³)
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? σ Γ Wᵢ i))
                     (match-define (-⟪α⟫ℓ ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                           [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                                 (.vector-ref ℒ (list (-W¹ Vᵥ* sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ
                                              (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵢ) (-W¹ Cᵢ cᵢ) ⟦k⟧))))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (-⟪α⟫ℓ ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for/union : (℘ -ς) ([C* (in-set (σ@ σ ⟪α⟫*))]
                               [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                     (.vector-ref ℒ (list (-W¹ Vᵥ* sᵥ) Wᵢ) Γ ⟪ℋ⟫ Σ
                                  (mon.c∷ l³ (ℒ-with-mon ℒ ℓ*) (-W¹ C* c*) ⟦k⟧)))])]
      [_
       (⟦k⟧ (-W (list (+●)) sₐ) Γ ⟪ℋ⟫ Σ)]))
  
  (def-ext (vector-set! ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ vector?] [Wᵢ integer?] [Wᵤ any/c])
    (match-define (-Σ σ _) Σ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (match-define (-W¹ Vᵤ sᵤ) Wᵤ)

    (match Vᵥ
      [(-Vector ⟪α⟫s)
       (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (σ⊕! Σ Γ ⟪α⟫ Wᵤ)
                  (⟦k⟧ (+W (list -void)) Γ* ⟪ℋ⟫ Σ))]
      [(-Vector^ α n)
       (σ⊕! Σ Γ α Wᵤ)
       (⟦k⟧ (+W (list -void)) Γ ⟪ℋ⟫ Σ)]
      [(-Vector/guard grd ⟪α⟫ᵥ l³)
       (match-define (-l³ l+ l- lo) l³)
       (define l³* (-l³ l- l+ lo))
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? σ Γ Wᵢ i))
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (match-define (-⟪α⟫ℓ ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                           [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                                 (define W-c (-W¹ Cᵢ cᵢ))
                                 (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                                 (define ⟦chk⟧ (mk-mon l³* (ℒ-with-mon ℒ ℓᵢ) (mk-rt W-c) (mk-rt Wᵤ)))
                                 (⟦chk⟧ ⊥ρ Γ* ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* (+W¹ 'vector-set!)) '() ⊥ρ ℒ ⟦k⟧))))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (-⟪α⟫ℓ ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for*/union : (℘ -ς) ([C*  (in-set (σ@ σ ⟪α⟫*))]
                                [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                      (define W-c (-W¹ C* c*))
                      (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                      (define ⟦chk⟧ (mk-mon l³* (ℒ-with-mon ℒ ℓ*) (mk-rt W-c) (mk-rt Wᵤ)))
                      (⟦chk⟧ ⊥ρ Γ ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* (+W¹ 'vector-set!)) '() ⊥ρ ℒ ⟦k⟧)))])]
      [_
       (⟦k⟧ (+W (list -void)) Γ ⟪ℋ⟫ Σ)]))
  
  (def-prim vector->list (vector? . -> . list?)) ; FIXME retain content
  (def-prim/custom (list->vector ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W list?])
    (match-define (-Σ σ _) Σ)
    (match-define (-W¹ Vₗ sₗ) W)
    (define Vₐ
      (match Vₗ
        ;; Collect content of non-empty list
        [(? -St? Vₗ)
         (define α (-α->⟪α⟫ (-α.vct ℒ ⟪ℋ⟫)))
         (for ([V (in-set (extract-list-content σ Vₗ))])
           (σ⊕V! Σ α V))
         (-Vector^ α (+● 'exact-positive-integer?))]
        ;; Empty list -> Empty vector
        [(-b (list))
         (-Vector '())]
        ;; Default
        [_ (+● 'vector?)]))
    {set (-ΓA (-Γ-facts Γ) (-W (list Vₐ) (?t@ 'vector->list sₗ)))})
  (def-prim/todo vector->immutable-vector
    (vector? . -> . (and/c vector? immutable?)))
  (def-prim/todo vector-fill!
    ((and/c vector? (not/c immutable?)) any/c . -> . void?))
  (def-prim/todo vector-copy! ; FIXME uses
    ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?))
  #;[vector->values ; FIXME uses, var-values, `any` instead of `any/c`
     (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any)]

  (def-ext build-vector
    (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c) . -> . vector?))

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
