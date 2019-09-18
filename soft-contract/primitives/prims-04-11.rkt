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
         racket/vector
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
         "../utils/map.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
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
          val^ sto^ cache^
          prover^
          exec^ app^ mon^)
  (export)
  
  (def-pred vector?)
  (def (make-vector Σ ℓ W)
    #:init ([Vₙ exact-nonnegative-integer?])
    #:rest [W (listof any/c)]
    (: make : V^ V^ → R)
    (define (make Vₙ Vᵥ)
      (match Vₙ
        [(-b (? index? n))
         (define α (α:dyn (β:vect-elems ℓ n) H₀))
         (R-of (Vect α) (alloc α (make-vector n Vᵥ)))]
        [(app (λ ([D : D]) (unpack D Σ)) Vₙ)
         (define α (α:dyn (β:vct ℓ) H₀))
         (R-of {set (Vect-Of α Vₙ)} (alloc α Vᵥ))]))
    (match W
      ['()       (make (unpack Vₙ Σ) {set -zero})]
      [(list Vᵥ) (make (unpack Vₙ Σ) (unpack Vᵥ Σ))]
      [_ (r:err! (Err:Arity 'make-vector W ℓ))
         ⊥R]))
  
  (def (vector Σ ℓ W)
    #:init ()
    #:rest [W (listof any/c)]
    (define S (list->vector (unpack-W W Σ)))
    (define α (α:dyn (β:vect-elems ℓ (vector-length S)) H₀))
    (R-of {set (Vect α)} (alloc α S)))
  (def vector-immutable
    (∀/c (α) (() #:rest (listof α) . ->* . (and/c (vectorof α) immutable?))))
  (def (vector-length Σ ℓ W)
    #:init ([V vector?])
    (R-of (set-union-map
           (match-lambda
             [(Vect (α:dyn (β:vect-elems _ n) _)) {set (-b n)}]
             [(Vect-Of _ Vₙ) Vₙ]
             [(Guarded _ (? Vect/C? C) _)
              (define-values (_₁ _₂ n) (Vect/C-fields C))
              {set (-b (assert n))}]
             [_ {set (-● {set 'index?})}])
           (unpack V Σ))))

  (def (vector-ref Σ ℓ W)
    #:init ([Vᵥ vector?] [Vᵢ exact-nonnegative-integer?])
    ((inst fold-ans/collapsing V)
     Σ
     (match-lambda
       [(Vect α)
        (define Vₐ
          (for/fold ([acc : V^ ∅])
                    ([(Vs i) (in-indexed (Σ@/blob α Σ))] #:when (maybe=? Σ i Vᵢ))
            (V⊔ acc Vs)))
        (R-of Vₐ)]
       [(Vect-Of α n)
        (R-of (Σ@ α Σ))]
       [(Guarded (cons l+ l-) G αᵥ)
        (define Vᵥ* (Σ@ αᵥ Σ))
        (match G
          [(? Vect/C?)
           (define-values (αₕ ℓₒ n) (Vect/C-fields G))
           (define (ref [i : Natural])
             (app Σ ℓₒ {set 'vector-ref} (list Vᵥ* {set (-b i)})))
           (define Cs (Σ@/blob αₕ Σ))
           (define ctx (Ctx l+ l- ℓₒ ℓ))
           (for/ans ([(Cᵢ i) (in-indexed Cs)] #:when (maybe=? Σ i Vᵢ))
             (with-collapsing/R Σ [(ΔΣ W) (ref (assert i index?))]
               (define Σ* (⧺ Σ ΔΣ))
               (ΔΣ⧺R ΔΣ (mon Σ* ctx Cᵢ (car (collapse-W^ Σ* W))))))]
          {(Vectof/C α* ℓₒ)
           (define ctx (Ctx l+ l- ℓₒ ℓ))
           (with-collapsing/R Σ [(ΔΣ W) (app Σ (Ctx-origin ctx) {set 'vector-ref} (list Vᵥ* Vᵢ))]
             (define Σ* (⧺ Σ ΔΣ))
             (ΔΣ⧺R ΔΣ (mon Σ* ctx (Σ@ α* Σ) (car (collapse-W^ Σ* W)))))})]
       [_ (R-of {set (-● ∅)})])
     (unpack Vᵥ Σ)))
  
  (def (vector-set! Σ ℓ W)
    #:init ([V^ vector?] [Vᵢ exact-nonnegative-integer?] [Vᵤ any/c])
    (define ΔΣ*
      (for/fold ([acc : ΔΣ ⊥ΔΣ]) ([V (in-set (unpack V^ Σ))])
        (match V
          [(Vect α)
           (define S (Σ@/blob α Σ))
           (define S* (vector-copy S))
           (define Vᵤ:unpacked (unpack Vᵤ Σ))
           (for ([(Vs i) (in-indexed S)] #:when (maybe=? Σ i Vᵢ))
             (vector-set! S* i Vᵤ:unpacked))
           (mut α S* Σ)]
          [(Vect-Of α _) (ΔΣ⊔ Σ acc (mut α (unpack Vᵤ Σ) Σ))]
          [(Guarded (cons l+ l-) G αᵥ)
           (define V*^ (Σ@ αᵥ Σ))
           (match G
             [(? Vect/C?)
              (define-values (αₕ ℓₒ n) (Vect/C-fields G))
              (define ctx* (Ctx l- l+ ℓₒ ℓ))
              (define Cs (Σ@/blob αₕ Σ))
              (for/fold ([acc : ΔΣ acc])
                        ([(Cᵢ i) (in-indexed Cs)] #:when (maybe=? Σ i Vᵢ))
                (with-collapsing Σ [(ΔΣ₀ Ws) (mon Σ ctx* Cᵢ Vᵤ)]
                  #:fail acc
                  (define Vᵤ* (car (collapse-W^ (⧺ Σ ΔΣ₀) Ws)))
                  (define Σ* (⧺ Σ ΔΣ₀))
                  (with-collapsing Σ* [(ΔΣ₁ _) (app Σ* ℓₒ {set 'vector-set!} (list V*^ {set (-b i)} Vᵤ*))]
                    #:fail acc
                    (ΔΣ⊔ Σ acc (⧺ ΔΣ₀ ΔΣ₁)))))]
             [(Vectof/C α* ℓₒ)
              (define ctx* (Ctx l- l+ ℓₒ ℓ))
              (with-collapsing Σ [(ΔΣ₀ Ws) (mon Σ ctx* (Σ@ α* Σ) Vᵤ)]
                #:fail acc
                (define Σ* (⧺ Σ ΔΣ₀))
                (define Vᵤ* (car (collapse-W^ Σ* Ws)))
                (with-collapsing Σ* [(ΔΣ₁ _) (app Σ* ℓₒ {set 'vector-set!} (list V*^ Vᵢ Vᵤ*))]
                  #:fail acc
                  (ΔΣ⊔ Σ* acc (⧺ ΔΣ₀ ΔΣ₁))))])]
          [_ acc])))
    (R-of -void ΔΣ*))
  
  (def vector->list (∀/c (α) ((vectorof α) . -> . (listof α))))
  (def list->vector (∀/c (α) ((listof α) . -> . (vectorof α))))
  
  (def vector->immutable-vector (∀/c (α) ((vectorof α) . -> . (and/c (vectorof α) immutable?))))
  (def vector-fill! ((and/c vector? (not/c immutable?)) any/c . -> . void?))
  (def vector-copy!
    (case->
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?]
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? exact-nonnegative-integer? . -> . void?]
     [(and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . void?]))
  (def vector->values ; FIXME uses, var-values, `any` instead of `any/c`
    (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any))

  (def build-vector (∀/c (α) (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . α) . -> . (vectorof α))))

  ;; 4.11.1 Additional Vector Functions
  (def vector-set*! ; FIXME uses
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

  (define-syntax for/ans
    (syntax-parser
      [(for/ans (clauses ...) body ...)
       (with-syntax ([R⊔ (format-id #'for/ans "R⊔")])
         #'(for/fold ([r : R ⊥R]) (clauses ...)
             (R⊔ r (let () body ...))))]))
  )
