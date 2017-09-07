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
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
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
  (import prim-runtime^ widening^ val^ pc^ compile^ proof-system^
          env^ sto^ kont^)
  (export)

  (def-pred vector?)
  (splicing-let
      ([.internal-make-vector
        (let ()
          (def (internal-make-vector ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
            #:init ([Wₙ exact-nonnegative-integer?]
                    [Wᵥ any/c])
            (define σ (-Σ-σ Σ))
            (match-define (-W¹ Vₙ sₙ) Wₙ)
            (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
            (define tₐ ℓ)
            ;; Heuristic: more concrete vector if length is available concretely
            (match sₙ
              [(-b (? exact-nonnegative-integer? n))
               (define ⟪α⟫s ; with side effect widening store
                 (for/list : (Listof ⟪α⟫) ([i (in-range n)])
                   (define ⟪α⟫ (-α->⟪α⟫ (-α.idx ℓ ⟪ℋ⟫ (assert i index?))))
                   (σ⊕! Σ Γ ⟪α⟫ Wᵥ)
                   ⟪α⟫))
               (⟦k⟧ (-W (list (-Vector ⟪α⟫s)) tₐ) $ Γ ⟪ℋ⟫ Σ)]
              [_
               (define ⟪α⟫ (-α->⟪α⟫ (-α.vct ℓ ⟪ℋ⟫)))
               (σ⊕! Σ Γ ⟪α⟫ Wᵥ) ; initializing, not mutating
               (⟦k⟧ (-W (list (-Vector^ ⟪α⟫ Vₙ)) tₐ) $ Γ ⟪ℋ⟫ Σ)]))
          .internal-make-vector)])
    (def (make-vector ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      #:init ()
      #:rest [Ws (listof any/c)]
      (define Ws*
        (match Ws
          [(list Wₙ) (list Wₙ (+W¹ -zero))]
          [_ Ws]))
      (.internal-make-vector ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)))
  
  (def (vector ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)]
    (define σ (-Σ-σ Σ))
    (define tₐ ℓ)
    (define-values ($* αs.rev) ; with side effect widening store
      (for/fold ([$ : -$ $]
                 [αs.rev : (Listof ⟪α⟫) '()])
                ([W (in-list Ws)]
                 [i (in-naturals)])
        (match-define (-W¹ V t) W)
        (define V* (V+ σ V (predicates-of Γ t)))
        (define α (-α->⟪α⟫ (-α.idx ℓ ⟪ℋ⟫ (assert i index?))))
        (σ⊕V! Σ α V*)
        (define l (-loc.offset 'vector (assert i index?) tₐ))
        (values ($-set! Σ $ α l t) (cons α αs.rev))))
    (⟦k⟧ (-W (list (-Vector (reverse αs.rev))) tₐ) $ Γ ⟪ℋ⟫ Σ))
  (def vector-immutable
    (∀/c (α) (() #:rest (listof α) . ->* . (and/c (vectorof α) immutable?))))
  (def (vector-length ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ([W vector?])
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'vector-length s))
    (define A
      (match V
        [(-Vector ⟪α⟫s) (list (-b (length ⟪α⟫s)))]
        [(-Vector^ _ n) (list n)]
        [(-Vector/guard (-Vector/C ⟪α⟫s) _ _) (list (-b (length ⟪α⟫s)))]
        [_ (list (+● 'exact-nonnegative-integer?))]))
    (⟦k⟧ (-W A sₐ) $ Γ ⟪ℋ⟫ Σ))

  (def (vector-ref ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ([Wᵥ vector?] [Wᵢ integer?])
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
                       (printf "  - ~a ↦ ~a~n" i (set-count (σ@ Σ ⟪α⟫))))
                     (printf "~n")))
       (for/union : (℘ -ς) ([⟪α⟫ : ⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (cond [sᵥ (define l (-loc.offset 'vector (assert i index?) sᵥ))
                            (define-values (Ws $*) ($@! Σ Γ ⟪α⟫ $ l ℓ))
                            (for/union : (℘ -ς) ([W (in-set Ws)])
                              (⟦k⟧ (W¹->W W) $* Γ* ⟪ℋ⟫ Σ))]
                        [else
                         (for/union : (℘ -ς) ([V (in-set (σ@ Σ ⟪α⟫))])
                           (⟦k⟧ (-W (list V) #f) $ Γ* ⟪ℋ⟫ Σ))]))]
      [(-Vector^ α n)
       (for/union : (℘ -ς) ([V (σ@ Σ α)])
                  (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ))]
      [(-Vector/guard grd ⟪α⟫ᵥ ctx)
       (define ℓ/ignore (ℓ-with-src ℓ 'vector-ref))
       (define lo (-ctx-src ctx))
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                     (match-define (-⟪α⟫ℓ ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ Σ ⟪α⟫ᵢ))]
                                           [⟦k⟧* (in-value (mon.c∷ (ctx-with-ℓ ctx ℓᵢ) (-W¹ Cᵢ cᵢ) ⟦k⟧))]
                                           [Vᵥ* (in-set (σ@ Σ ⟪α⟫ᵥ))])
                        (.vector-ref ℓ/ignore (list (-W¹ Vᵥ* sᵥ) Wᵢ) $ Γ* ⟪ℋ⟫ Σ ⟦k⟧*)))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (-⟪α⟫ℓ ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for*/union : (℘ -ς) ([C* (in-set (σ@ Σ ⟪α⟫*))]
                                [⟦k⟧* (in-value (mon.c∷ (ctx-with-ℓ ctx ℓ*) (-W¹ C* c*) ⟦k⟧))]
                                [Vᵥ* (in-set (σ@ Σ ⟪α⟫ᵥ))])
            (.vector-ref ℓ/ignore (list (-W¹ Vᵥ* sᵥ) Wᵢ) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))])]
      [_
       (⟦k⟧ (-W (list (+●)) sₐ) $ Γ ⟪ℋ⟫ Σ)]))
  
  (def (vector-set! ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ([Wᵥ vector?] [Wᵢ integer?] [Wᵤ any/c])
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (match-define (-W¹ Vᵤ sᵤ) Wᵤ)

    (match Vᵥ
      [(-Vector ⟪α⟫s)
       (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (σ⊕! Σ Γ ⟪α⟫ Wᵤ)
                  (define $*
                    (if sᵥ
                        ($-set! Σ $ ⟪α⟫ (-loc.offset 'vector (assert i index?) sᵥ) sᵤ)
                        ($-del* $ (get-aliases Σ ⟪α⟫))))
                  (⟦k⟧ (+W (list -void)) $* Γ* ⟪ℋ⟫ Σ))]
      [(-Vector^ α n)
       (σ⊕! Σ Γ α Wᵤ)
       (⟦k⟧ (+W (list -void)) $ Γ ⟪ℋ⟫ Σ)]
      [(-Vector/guard grd ⟪α⟫ᵥ ctx)
       (define ctx* (ctx-neg ctx))
       (define ℓ/ignore (ℓ-with-src ℓ 'vector-set!))
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? (-Σ-σ Σ) Γ Wᵢ i))
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (match-define (-⟪α⟫ℓ ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ Σ ⟪α⟫ᵢ))]
                                           [Vᵥ* (in-set (σ@ Σ ⟪α⟫ᵥ))])
                                 (define W-c (-W¹ Cᵢ cᵢ))
                                 (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                                 (define ⟦chk⟧ (mk-mon (ctx-with-ℓ ctx* ℓᵢ) (mk-rt W-c) (mk-rt Wᵤ)))
                                 (⟦chk⟧ ⊥ρ $ Γ* ⟪ℋ⟫ Σ
                                  (ap∷ (list Wᵢ Wᵥ* (+W¹ 'vector-set!)) '() ⊥ρ ℓ/ignore ⟦k⟧))))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (-⟪α⟫ℓ ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for*/union : (℘ -ς) ([C*  (in-set (σ@ Σ ⟪α⟫*))]
                                [Vᵥ* (in-set (σ@ Σ ⟪α⟫ᵥ))])
                      (define W-c (-W¹ C* c*))
                      (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                      (define ⟦chk⟧ (mk-mon (ctx-with-ℓ ctx* ℓ*) (mk-rt W-c) (mk-rt Wᵤ)))
                      (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
                       (ap∷ (list Wᵢ Wᵥ* (+W¹ 'vector-set!)) '() ⊥ρ ℓ/ignore ⟦k⟧)))])]
      [_
       (⟦k⟧ (+W (list -void)) $ Γ ⟪ℋ⟫ Σ)]))
  
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
    (∀/c (α) ((α . -> . any/c) (vectorof α) . -> . (vectorof α))))
  (def vector-count ; FIXME varargs
    (∀/c (α) ((α . -> . any/c) (vectorof α) . -> . exact-nonnegative-integer?)))
  (def* (vector-argmin vector-argmax) (∀/c (α) ((α . -> . real?) (vectorof α) . -> . α)))
  (def* (vector-member vector-memv vector-memq) (any/c vector? . -> . (or/c exact-nonnegative-integer? not)))
  )
