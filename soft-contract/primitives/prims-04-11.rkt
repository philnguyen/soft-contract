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
  (splicing-let
      ([.internal-make-vector
        (let ()
          (def (internal-make-vector Σ ℓ W)
            #:init ([Vₙ exact-nonnegative-integer?]
                    [Vᵥ any/c])
            (match Vₙ
              [(singleton-set (-b (? exact-nonnegative-integer? n)))
               (define-values (αs ΔΣ) (alloc-each (make-list n Vᵥ) (λ (i) (β:idx ℓ i))))
               (r:just (Vect αs) ΔΣ)]
              [_
               (define α (α:dyn (β:vct ℓ) H₀))
               (r:just (Vect-Of α Vₙ) (alloc α Vᵥ))]))
          .internal-make-vector)])
    (def (make-vector Σ ℓ W)
      #:init ()
      #:rest [W (listof any/c)]
      (define W* (match W
                   [(list Vₙ) (list Vₙ {set (-b 0)})]
                   [_ W]))
      (.internal-make-vector Σ ℓ W*)))
  
  (def (vector Σ ℓ W)
    #:init ()
    #:rest [W (listof any/c)]
    (define-values (αs ΔΣ) (alloc-each W (λ (i) (β:idx ℓ i))))
    (r:just (Vect αs) ΔΣ))
  (def vector-immutable
    (∀/c (α) (() #:rest (listof α) . ->* . (and/c (vectorof α) immutable?))))
  (def (vector-length Σ ℓ W)
    #:init ([V vector?])
    (just (set-union-map
           (match-lambda
             [(Vect αs) {set (-b (length αs))}]
             [(Vect-Of _ Vₙ) Vₙ]
             [(Guarded _ (Vect/C αs _) _) {set (-b (length αs))}]
             [_ {set (-● {set 'exact-nonnegative-integer?})}])
           V)))

  (def (vector-ref Σ ℓ W)
    #:init ([Vᵥ vector?] [Vᵢ exact-nonnegative-integer?])
    ((inst fold-ans V)
     (match-lambda
       [(Vect αs)
        (define Vₐ
          (for/fold ([acc : V^ ∅])
                    ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
            (∪ acc (unpack αᵢ Σ))))
        (r:just Vₐ)]
       [(Vect-Of α n)
        (r:just (unpack α Σ))]
       [(Guarded (cons l+ l-) G αᵥ)
        (define Vᵥ* (unpack αᵥ Σ)) 
        (match G
          [(Vect/C αs ℓₒ)
           (define (ref [i : Natural])
             (app Σ ℓₒ {set 'vector-ref} (list Vᵥ* {set (-b i)})))
           (define ctx (Ctx l+ l- ℓₒ ℓ))
           (for/ans ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
             (with-collapsing/R [(ΔΣ W) (ref (assert i index?))]
               (with-pre ΔΣ (mon (⧺ Σ ΔΣ) ctx (unpack αᵢ Σ) (car (collapse-W^ W))))))]
          {(Vectof/C α* ℓₒ)
           (define ctx (Ctx l+ l- ℓₒ ℓ))
           (with-collapsing/R [(ΔΣ W) (app Σ (Ctx-origin ctx) {set 'vector-ref} (list Vᵥ* Vᵢ))]
             (with-pre ΔΣ
               (mon (⧺ Σ ΔΣ) ctx (unpack α* Σ) (car (collapse-W^ W)))))})]
       [_ (r:just (-● ∅))])
     (unpack Vᵥ Σ)))
  
  (def (vector-set! Σ ℓ W)
    #:init ([V^ vector?] [Vᵢ exact-nonnegative-integer?] [Vᵤ any/c])
    (define-values (ΔΣ* es*)
      (for/fold ([acc : ΔΣ ⊥ΔΣ] [es : (℘ Err) ∅]) ([V (in-set V^)])
        (match V
          [(Vect αs)
           (values (for/fold ([acc : ΔΣ acc])
                             ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
                     (ΔΣ⊔ acc (mut αᵢ Vᵤ)))
                   es)]
          [(Vect-Of α _) (values (ΔΣ⊔ acc (mut α Vᵤ)) es)]
          [(Guarded (cons l+ l-) G αᵥ)
           (define V*^ (unpack αᵥ Σ))
           (match G
             [(Vect/C αs ℓₒ)
              (define ctx* (Ctx l- l+ ℓₒ ℓ))
              (for/fold ([acc : ΔΣ acc] [es : (℘ Err) es])
                        ([(αᵢ i) (in-indexed αs)] #:when (maybe=? Σ i Vᵢ))
                (with-collapsing [(ΔΣ₀ Ws) (mon Σ ctx* (unpack αᵢ Σ) Vᵤ)]
                  #:fail acc
                  (define Vᵤ* (car (collapse-W^ Ws)))
                  (with-collapsing [(ΔΣ₁ _) (app (⧺ Σ ΔΣ₀) ℓₒ {set 'vector-set!} (list V*^ {set (-b i)} Vᵤ*))]
                    #:fail acc
                    (values (ΔΣ⊔ acc (⧺ ΔΣ₀ ΔΣ₁)) es))))]
             [(Vect-Of α* ℓₒ)
              (define ctx* (Ctx l- l+ ℓₒ ℓ))
              (with-collapsing [(ΔΣ₀ Ws) (mon Σ ctx* (unpack α* Σ) Vᵤ)]
                #:fail acc
                (define Vᵤ* (car (collapse-W^ Ws)))
                (with-collapsing [(ΔΣ₁ _) (app (⧺ Σ ΔΣ₀) ℓₒ {set 'vector-set} V*^ Vᵢ Vᵤ*)]
                  (values (ΔΣ⊔ acc (⧺ ΔΣ₀ ΔΣ₁)) ∅)))])]
          [_ (values acc es)])))
    (values (hash ΔΣ* {set (list {set -void})}) es*))
  
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
  )
