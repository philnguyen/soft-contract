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
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "../reduction/signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-16@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.16 Sets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-16@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^
          kont^ mon^)
  (export)

  ;;;;; Hash Sets
  (def-preds (set-equal? set-eqv? set-eq? set? set-mutable? set-weak?))
  (def-prim/custom (set ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    (define α (-α->⟪α⟫ (-α.set.elem ℓ ⟪ℋ⟫)))
    (σ⊕Vs! Σ α ∅)
    (for ([W (in-list Ws)])
      (σ⊕! Σ Γ α W))
    {set (-ΓA Γ (-W (list (-Set^ α #t)) (apply ?t@ 'set (map -W¹-t Ws))))})
  (def-prim/todo seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set?)))
  (def-prim/todo seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set?)))
  (def-prim/todo mutable-set
    (() #:rest list? . ->* . (and/c generic-set? set-equal? set-mutable?)))
  (def-prim/todo mutable-seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-mutable?)))
  (def-prim/todo mutable-seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set-mutable?)))
  (def-prim/todo weak-set
    (() #:rest list? . ->* . (and/c generic-set? set-equal? set-weak?)))
  (def-prim/todo weak-seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-weak?)))
  (def-prim/todo weak-seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set-weak?)))
  (def-prim list->set
    (list? . -> . (and/c generic-set? set-equal? set?)))
  (def-prim/todo list->seteqv
    (list? . -> . (and/c generic-set? set-eqv? set?)))
  (def-prim/todo list->seteq
    (list? . -> . (and/c generic-set? set-eq? set?)))
  (def-prim/todo list->mutable-set
    (list? . -> . (and/c generic-set? set-equal? set-mutable?)))
  (def-prim/todo list->mutable-seteqv
    (list? . -> . (and/c generic-set? set-eqv? set-mutable?)))
  (def-prim/todo list->mutable-seteq
    (list? . -> . (and/c generic-set? set-eq? set-mutable?)))
  (def-prim/todo list->weak-set
    (list? . -> . (and/c generic-set? set-equal? set-weak?)))
  (def-prim/todo list->weak-seteqv
    (list? . -> . (and/c generic-set? set-eqv? set-weak?)))
  (def-prim/todo list->weak-seteq
    (list? . -> . (and/c generic-set? set-eq? set-weak?)))

;;;;; 4.16.2 Set Predicates and Contracts
  (def-pred generic-set?)
  #;[set-implements ; FIXME listof
     ((generic-set?) #:rest (listof symbol?) . ->* . boolean?)]
  #;[set-implements/c ; FIXME varargs, contract?
     (symbol? . -> . flat-contract?)]
  (def-prim/custom (set/c ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([W contract? #|TODO chaperone-contract?|#])
    (match-define (-W¹ _ t) W)
    (define α (-α->⟪α⟫ (-α.set/c-elem ℓ ⟪ℋ⟫)))
    (σ⊕! Σ Γ α W)
    (define C (-Set/C (-⟪α⟫ℓ α (ℓ-with-id ℓ 'set/c))))
    {set (-ΓA Γ (-W (list C) (?t@ 'set/c t)))})

;;;;; 4.16.3 Generic Set Interface

  ;; 4.16.3.1 Set Methods
  (def-pred set-member? (generic-set? any/c))
  (def-ext (set-add ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₛ set? #|TODO generic-set?|#]
              [Wₑ any/c])
    (match-define (-W¹ Vₛ tₛ) Wₛ)
    (match-define (-W¹ Vₑ tₑ) Wₑ)
    (define tₐ (?t@ 'set-add tₛ tₑ))
    (define αₑ* (-α->⟪α⟫ (-α.set.elem ℓ ⟪ℋ⟫)))
    (match Vₛ
      [(-Set^ αₑ _)
       (σ-copy! Σ αₑ αₑ*)
       (σ⊕! Σ Γ αₑ* Wₑ)
       (define Wₕ* (-W (list (-Set^ αₑ* #t)) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]
      [(-Set/guard (and C (-Set/C (-⟪α⟫ℓ αₚ ℓₚ))) αₛ* ctx)
       (define ctx* (ctx-neg ctx))
       (define ⟦k⟧* (set-add-inner∷ ℓ αₛ* tₛ (wrap-set∷ C ctx ⟦k⟧)))
       (for*/union : (℘ -ς) ([C (in-set (σ@ Σ αₚ))])
         (mon (ctx-with-ℓ ctx* ℓₚ) (-W¹ C #f) Wₑ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
      [_
       (define Wₕ* (-W (list (-Set^ ⟪α⟫ₒₚ #t)) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]))
  (def-prim/custom (set-remove ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([Wₛ set?] [Wₑ any/c])
    {set (-ΓA Γ (W¹->W Wₛ))})
  [def-prims (set-add! set-remove!)
    ((and/c generic-set? set-mutable?) any/c . -> . void?)]
  [def-pred set-empty? (generic-set?)]
  (def-prim/todo set-count
    (generic-set? . -> . exact-nonnegative-integer?))
  (def-ext (set-first ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₛ set? #|TODO|#])
    (match-define (-W¹ Vₛ tₛ) Wₛ)
    (define tₐ (?t@ 'set-first tₛ))
    (match Vₛ
      [(-Set^ α _)
       (for/union : (℘ -ς) ([V (in-set (σ@ Σ α))])
         (⟦k⟧ (-W (list V) tₐ) $ Γ ⟪ℋ⟫ Σ))]
      [(-Set/guard (-Set/C (-⟪α⟫ℓ αₑ ℓₑ)) αₛ* ctx)
       (for*/union : (℘ -ς) ([C (in-set (σ@ Σ αₑ))]
                             [Vₛ* (in-set (σ@ Σ αₛ*))])
         (define ⟦k⟧* (mon.c∷ (ctx-with-ℓ ctx ℓₑ) (-W¹ C #f) ⟦k⟧))
         (define Wₛ* (-W¹ Vₛ* tₛ))
         (.set-first ℓ (list Wₛ*) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
      [_ (⟦k⟧ (-W (list (+●)) tₐ) $ Γ ⟪ℋ⟫ Σ)]))
  (def-prim/custom (set-rest ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([Wₛ set? #|TODO|#])
    {set (-ΓA Γ (W¹->W Wₛ))})
  (def-prim/todo set->stream
    (generic-set? . -> . stream?))
  (def-prim/todo set-copy
    (generic-set? . -> . generic-set?))
  (def-prim/todo set-copy-clear
    (generic-set? . -> . (and/c generic-set? set-empty?)))
  (def-prim/todo set-clear
    ((and/c generic-set? (not/c set-mutable?)) . -> . (and/c generic-set? set-empty?)))
  (def-prim/todo set-clear!
    ((and/c generic-set? set-mutable?) . -> . void?))
  ;; FIXME listof

  (def-prim set-union
    ; FIXME enforce sets of the same type
    ; FIXME uses
    #;((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)
    (set? set? . -> . set?))
  #|
  (def-prim/todo set-union! ; FIXME enforce sets of the same type
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-intersect
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-intersect!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-subtract
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-subtract!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-symmetric-difference
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-symmetric-difference!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))|#
  (def-prims (set=? subset? proper-subset?) ; FIXME enforce same `set` type
    (generic-set? generic-set? . -> . boolean?))
  (def-prim/custom (set->list ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([Wₛ set?])
    (error 'set->list "TODO"))
  #;[set-map ; FIXME listof
     (generic-set? (any/c . -> . any/c) . -> . (listof any/c))]
  (def-prim/todo set-for-each
    (generic-set? (any/c . -> . any) . -> . void?))
  (def-prim in-set
    (generic-set? . -> . sequence?))

;;;;; 4.16.4 Custom Hash Sets
  #;[make-custom-set-types ; FIXME uses
     ((or/c (any/c any/c . -> . any/c)
            (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
      . -> .
      (values (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              ([] [stream?] . ->* . generic-set?)
              ([] [stream?] . ->* . generic-set?)
              ([] [stream?] . ->* . generic-set?)))]
  )
