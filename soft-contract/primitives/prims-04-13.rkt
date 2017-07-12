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

(provide prims-04-13@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.13 Hash Tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-13@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^ instr^ kont^)
  (export)

  (def-pred hash?)
  (def-prims (hash-equal? hash-eqv? hash-eq? hash-weak?)
    (hash? . -> . boolean?))

  (splicing-local
      ((: hash-helper : -⟪ℋ⟫ -ℒ -Σ -Γ (Listof -W¹) Symbol -h → (℘ -ΓA))
       (define (hash-helper ⟪ℋ⟫ ℒ Σ Γ Ws name eq)
         (define A
           (cond
             [(even? (length Ws))
              (define αₖ (-α->⟪α⟫ (-α.hash.key ℒ ⟪ℋ⟫)))
              (define αᵥ (-α->⟪α⟫ (-α.hash.val ℒ ⟪ℋ⟫)))
              (let go! ([Ws : (Listof -W¹) Ws])
                (match Ws
                  [(list* Wₖ Wᵥ Ws*)
                   (σ⊕! Σ Γ αₖ Wₖ)
                   (σ⊕! Σ Γ αᵥ Wᵥ)
                   (go! Ws*)]
                  ['() (void)]))
              (define V (-Hash^ αₖ αᵥ #t))
              (-W (list V) (apply ?t@ name (map -W¹-t Ws)))]
             [else
              (define-values (ℓ l) (unpack-ℒ ℒ))
              (-blm l name (list (string->symbol "even number of arg(s)")) (map -W¹-V Ws) ℓ)]))
         {set (-ΓA Γ A)}))
    (def-prim/custom (hash ⟪ℋ⟫ ℒ Σ $ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Σ Γ Ws 'hash 'hash-equal?))
    (def-prim/custom (hasheq ⟪ℋ⟫ ℒ Σ $ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Σ Γ Ws 'hasheq 'hash-eq?))
    (def-prim/custom (hasheqv ⟪ℋ⟫ ℒ Σ $ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Σ Γ Ws 'hasheqv 'hash-eqv?)))

  (splicing-local
      ;; FIXME the only reason for this hack is because the DSL doesn't have case-> yet
      ((define-syntax-parser define-make-hash
         [(_ make-hash:id eq:id #:immutable? immut?:boolean)
          (define/with-syntax make-hash-1 (format-id #'make-hash "~a-1" (syntax-e #'make-hash)))
          (define/with-syntax .make-hash-1 (format-id #'make-hash ".~a-1" (syntax-e #'make-hash)))
          (define/with-syntax ctc-immut?
            (if (syntax-e #'immut?) #'immutable? #'(not/c immutable?)))
          (define/with-syntax refine-immut?
            (if (syntax-e #'immut?) #''immutable? #'(-not/c 'immutable?)))
          #'(begin
              (def-prim make-hash-1
                ((listof pair?) . -> . (and/c hash? ctc-immut? eq)))
              (def-prim/custom (make-hash ⟪ℋ⟫ ℒ Σ $ Γ Ws)
                (match Ws
                  ['() {set (-ΓA Γ (-W (list (-● {set 'hash? 'eq refine-immut?}))
                                                  (apply ?t@ 'make-hash (map -W¹-t Ws))))}]
                  [_ (.make-hash-1 ⟪ℋ⟫ ℒ Σ $ Γ Ws)])))])
       )
    (define-make-hash make-hash hash-equal? #:immutable? #f)
    (define-make-hash make-hasheqv hash-eqv? #:immutable? #f)
    (define-make-hash make-hasheq hash-eq? #:immutable? #f)
    (define-make-hash make-immutable-hash hash-equal? #:immutable? #t)
    (define-make-hash make-immutable-hasheqv hash-eqv? #:immutable? #t)
    (define-make-hash make-immutable-hasheq hash-eq? #:immutable? #t))

  (def-prim make-weak-hash ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-equal? hash-weak?)))
  (def-prim make-weak-hasheqv ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-eqv? hash-weak?)))
  (def-prim make-weak-hasheq ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-eq? hash-weak?)))
  (def-prim/todo hash-set!
    ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
  (def-prim/todo hash-set*! ; FIXME uses
    ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
  (def-ext (hash-set ℒ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₕ (and/c hash? immutable?)]
              [Wₖ any/c]
              [Wᵥ any/c])
    (match-define (-W¹ Vₕ tₕ) Wₕ)
    (match-define (-W¹ _  tₖ) Wₖ)
    (match-define (-W¹ _  tᵥ) Wᵥ)
    (define tₐ (?t@ 'hash-set tₕ tₖ tᵥ))
    (define αₖ* (-α->⟪α⟫ (-α.hash.key ℒ ⟪ℋ⟫)))
    (define αᵥ* (-α->⟪α⟫ (-α.hash.val ℒ ⟪ℋ⟫)))
    (match Vₕ
      [(-Hash^ αₖ αᵥ _)
       (σ-copy! Σ αₖ αₖ*)
       (σ-copy! Σ αᵥ αᵥ*)
       (σ⊕! Σ Γ αₖ* Wₖ)
       (σ⊕! Σ Γ αᵥ* Wᵥ)
       (define Vₕ* (-Hash^ αₖ* αᵥ* #t))
       (define Wₕ* (-W (list Vₕ*) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]
      [(-Hash/guard C αₕ l³)
       (define-values (Vsₖ Vsᵥ) (collect-hash-pairs (-Σ-σ Σ) αₕ))
       (σ⊕Vs! Σ αₖ* Vsₖ)
       (σ⊕Vs! Σ αᵥ* Vsᵥ)
       (σ⊕! Σ Γ αₖ* Wₖ)
       (σ⊕! Σ Γ αᵥ* Wᵥ)
       (define Vₕ* (-Hash^ αₖ* αᵥ* #t))
       (define Wₕ* (-W (list Vₕ*) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]
      [_
       (define Wₕ* (-W (list (-Hash^ ⟪α⟫ₒₚ ⟪α⟫ₒₚ #t)) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]))
  (def-prim/todo hash-set* ; FIXME refine with `eq?` and `eqv?`
    ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?)))
  (def-ext (hash-ref ℒ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₕ hash?] [Wₖ any/c]) ; FIXME uses
    (match-define (-W¹ Vₕ tₕ) Wₕ)
    (match-define (-W¹ _  tₖ) Wₖ)
    (define tₐ (?t@ 'hash-ref tₕ tₖ))
    (match Vₕ
      [(-Hash^ _ αᵥ _)
       (for/union : (℘ -ς) ([V (in-set (σ@ Σ αᵥ))])
                  (⟦k⟧ (-W (list V) tₐ) $ Γ ⟪ℋ⟫ Σ))]
      [(-Hash/guard (-Hash/C _ (-⟪α⟫ℓ αᵥ ℓᵥ)) αₕ l³)
       (for*/union : (℘ -ς) ([Cᵥ (in-set (σ@ Σ αᵥ))]
                             [Vₕ* (in-set (σ@ Σ αₕ))])
          (define ⟦k⟧* (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵥ) (-W¹ Cᵥ #|TODO|# #f) ⟦k⟧))
          (define Wₕ* (-W¹ Vₕ* tₕ))
          (.hash-ref ℒ (list Wₕ* Wₖ) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
      [_ (⟦k⟧ (-W (list (+●)) tₐ) $ Γ ⟪ℋ⟫ Σ)]))
  (def-prim hash-ref! ; FIXME precision
    (hash? any/c any/c . -> . any/c))
  (def-prim hash-has-key?
    (hash? any/c . -> . boolean?))
  (def-prim hash-update! ; FIXME uses
    ((and/c hash? (not/c immutable?)) any/c #|FIXME ext|# procedure? . -> . void?))
  (def-prim hash-update
    ((and/c hash? immutable?) any/c #|FIXME ext|# procedure? . -> . (and/c hash? immutable?)))
  (def-prim hash-remove!
    ((and/c hash? (not/c immutable?)) any/c . -> . void?))
  (def-prim/custom (hash-remove ⟪ℋ⟫ ℒ Σ $ Γ Ws)
    #:domain ([Wₕ hash?] [Wₖ any/c])
    {set (-ΓA Γ (W¹->W Wₕ))})
  (def-prim hash-clear!
    ((and/c hash? (not/c immutable?)) . -> . void?))
  (def-prim hash-clear
    ((and/c hash? immutable?) . -> . (and/c hash? immutable?)))
  (def-prim hash-copy-clear
    (hash? . -> . hash?))
  #;[hash-map ; FIXME uses ; FIXME listof
     (hash? (any/c any/c . -> . any/c) . -> . (listof any/c))]
  #;[hash-keys ; FIXME listof
     (hash? . -> . (listof any/c))]
  #;[hash-values ; FIXME listof
     (hash? . -> . (listof any/c))]
  #;[hash->list ; simplified from doc's `(cons/c any/c any/c)` ; FIXME listof
     (hash? . -> . (listof pair?))]
  (def-prim hash-for-each ; FIXME uses
    (hash? #|FIXME ext|# procedure? . -> . void?))
  (def-prim hash-count
    (hash? . -> . exact-nonnegative-integer?))
  (def-prim hash-empty?
    (hash? . -> . boolean?))
  (def-prim hash-iterate-first
    (hash? . -> . (or/c exact-nonnegative-integer? not)))
  (def-prim hash-iterate-next
    (hash? exact-nonnegative-integer? . -> . (or/c exact-nonnegative-integer? not)))
  (def-prims (hash-iterate-key hash-iterate-value)
    (hash? exact-nonnegative-integer? . -> . any/c))
  (def-prim hash-copy
    (hash? . -> . (and/c hash? (not/c immutable?))))
  (def-prims (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
    (any/c . -> . fixnum?))

  ;; 4.13.1 Additional Hash Table Functions
  ; FIXME wtf is `hash-can-functional-set?`
  ;[hash-union ]
  ;[hash-union!]
  )
