#lang typed/racket/base

(provide exts-04@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/contract
         set-extras
         "../utils/function.rkt"
         "../ast/definition.rkt"
         "../ast/shorthands.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "../reduction/signatures.rkt"
         "../primitives/signatures.rkt"
         "signatures.rkt"
         "def-ext.rkt")

(define-unit exts-04@
  (import ext-runtime^ prim-runtime^ proof-system^ widening^ app^ kont^ compile^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.9 Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-ext (map $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    ; FIXME uses 
    #:domain ([Wₚ (any/c . -> . any/c)]
              [Wₗ list?])
    (match-define (-Σ σ _ M) Σ)
    (match-define (-W¹ Vₚ sₚ) Wₚ)
    (match-define (-W¹ Vₗ sₗ) Wₗ)
    (define tₐ (?t@ 'map sₚ sₗ))
    (match Vₗ
      [(-b '()) (⟦k⟧ (-W (list -null) tₐ) $ Γ ⟪ℋ⟫ Σ)]
      [(-Cons _ _)
       (define ⟦k⟧* (mk-listof∷ tₐ ℒ ⟪ℋ⟫ ⟦k⟧))
       (for/union : (℘ -ς) ([V (extract-list-content σ Vₗ)])
                  (app $ ℒ Wₚ (list (-W¹ V #f)) Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
      [_ (⟦k⟧ (-W (list (-● (set 'list?))) tₐ) $ Γ ⟪ℋ⟫ Σ)]))

  (def-ext (for-each $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₚ (any/c . -> . any/c)]
              [Wₗ list?])
    #:result -void.Vs)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  #;(define cache : (HashTable Any Void) (make-hash))

  (def-ext (vector-ref $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ vector?] [Wᵢ integer?])
    (match-define (-Σ σ _ M) Σ)
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
                           #:when (plausible-index? M σ Γ Wᵢ i))
                       (printf "  - ~a ↦ ~a~n" i (set-count (σ@ σ ⟪α⟫))))
                     (printf "~n")))
       (for/union : (℘ -ς) ([⟪α⟫ : ⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? M σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (for/union : (℘ -ς) ([V (in-set (σ@ σ ⟪α⟫))])
                             (⟦k⟧ (-W (list V) sₐ) $ Γ* ⟪ℋ⟫ Σ)))]
      [(-Vector^ α n)
       (for/union : (℘ -ς) ([V (σ@ σ α)])
                  (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ))]
      [(-Vector/guard grd ⟪α⟫ᵥ l³)
       (match-define (-l³ _ _ lo) l³)
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? M σ Γ Wᵢ i))
                     (match-define (cons ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                           [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                                 (.vector-ref $ ℒ (list (-W¹ Vᵥ* sᵥ) Wᵢ) Γ* ⟪ℋ⟫ Σ
                                              (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵢ) (-W¹ Cᵢ cᵢ) ⟦k⟧))))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (cons ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for/union : (℘ -ς) ([C* (in-set (σ@ σ ⟪α⟫*))]
                               [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                     (.vector-ref $ ℒ (list (-W¹ Vᵥ* sᵥ) Wᵢ) Γ ⟪ℋ⟫ Σ
                                  (mon.c∷ l³ (ℒ-with-mon ℒ ℓ*) (-W¹ C* c*) ⟦k⟧)))])]
      [_
       (⟦k⟧ (-W -●.Vs sₐ) $ Γ ⟪ℋ⟫ Σ)]))

  (def-ext (vector-set! $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wᵥ vector?] [Wᵢ integer?] [Wᵤ any/c])
    (match-define (-Σ σ _ M) Σ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ Vᵢ sᵢ) Wᵢ)
    (match-define (-W¹ Vᵤ sᵤ) Wᵤ)

    (match Vᵥ
      [(-Vector ⟪α⟫s)
       (for/union : (℘ -ς) ([⟪α⟫ (in-list ⟪α⟫s)]
                            [i : Natural (in-naturals)]
                            #:when (plausible-index? M σ Γ Wᵢ i))
                  (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                  (σ⊕! Σ Γ ⟪α⟫ Wᵤ #:mutating? #t)
                  (⟦k⟧ -void.W $ Γ* ⟪ℋ⟫ Σ))]
      [(-Vector^ α n)
       (σ⊕! Σ Γ α Wᵤ #:mutating? #t)
       (⟦k⟧ -void.W $ Γ ⟪ℋ⟫ Σ)]
      [(-Vector/guard grd ⟪α⟫ᵥ l³)
       (match-define (-l³ l+ l- lo) l³)
       (define l³* (-l³ l- l+ lo))
       (match grd
         [(-Vector/C ⟪α⟫ℓs)
          (for/union : (℘ -ς) ([⟪α⟫ℓ (in-list ⟪α⟫ℓs)]
                               [i : Natural (in-naturals)]
                               #:when (plausible-index? M σ Γ Wᵢ i))
                     (define Γ* (Γ+ Γ (?t@ '= sᵢ (-b i))))
                     (match-define (cons ⟪α⟫ᵢ ℓᵢ) ⟪α⟫ℓ)
                     (define cᵢ #f #;(⟪α⟫->s ⟪α⟫ᵢ))
                     (for*/union : (℘ -ς) ([Cᵢ (in-set (σ@ σ ⟪α⟫ᵢ))]
                                           [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                                 (define W-c (-W¹ Cᵢ cᵢ))
                                 (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                                 (define ⟦chk⟧ (mk-mon l³* (ℒ-with-mon ℒ ℓᵢ) (mk-rt W-c) (mk-rt Wᵤ)))
                                 (⟦chk⟧ ⊥ρ $ Γ* ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* -vector-set!.W¹) '() ⊥ρ ℒ ⟦k⟧))))]
         [(-Vectorof ⟪α⟫ℓ)
          (match-define (cons ⟪α⟫* ℓ*) ⟪α⟫ℓ)
          (define c* #f #;(⟪α⟫->s ⟪α⟫*))
          (for*/union : (℘ -ς) ([C*  (in-set (σ@ σ ⟪α⟫*))]
                                [Vᵥ* (in-set (σ@ σ ⟪α⟫ᵥ))])
                      (define W-c (-W¹ C* c*))
                      (define Wᵥ* (-W¹ Vᵥ* sᵥ))
                      (define ⟦chk⟧ (mk-mon l³* (ℒ-with-mon ℒ ℓ*) (mk-rt W-c) (mk-rt Wᵤ)))
                      (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (ap∷ (list Wᵢ Wᵥ* -vector-set!.W¹) '() ⊥ρ ℒ ⟦k⟧)))])]
      [_
       (⟦k⟧ -void.W $ Γ ⟪ℋ⟫ Σ)]))

  (def-ext build-vector
    (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c) . -> . vector?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Sequences and Streams
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  #;(def-ext in-producer (procedure? . -> . sequence?))
  )
