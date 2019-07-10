#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         (only-in racket/function curry)
         set-extras
         unreachable
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(require typed/racket/unsafe)
(unsafe-require/typed racket/hash
  [hash-union (∀ (α β) ([(Immutable-HashTable α β)]
                        [#:combine (β β → β)]
                        #:rest (Immutable-HashTable α β)
                        . ->* .
                        (Immutable-HashTable α β)))])

(define-unit cache@
  (import sto^ val^)
  (export cache^)

  (define ⊥A : (Pairof R (℘ Err)) (cons ⊥R ∅))

  (: R-of ([(U D W)] [(U ΔΣ (℘ ΔΣ))] . ->* . R))
  (define (R-of x [ΔΣ ⊥ΔΣ])
    (define (with [A : W])
      (cond [(not (set? ΔΣ)) (hash A {set ΔΣ})]
            [(set-empty? ΔΣ) ⊥R]
            [else (hash A ΔΣ)]))
    (cond [(list? x) (with x)]
          [(and (set? x) (set-empty? x)) ⊥R]
          [else (with (list x))]))

  (: ΔΣ⧺R : ΔΣ R → R)
  (define (ΔΣ⧺R ΔΣ R)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ ΔΣ₀)) R)]))

  (: R⧺ΔΣ : R ΔΣ → R)
  (define (R⧺ΔΣ R ΔΣ)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ₀ ΔΣ)) R)])) 

  (: collapse-R/ΔΣ : Σ R → (Option ΔΣ))
  (define (collapse-R/ΔΣ Σ R)
    (match (hash-values R)
      ['() #f]
      [(cons ΔΣs₀ ΔΣs*) (foldl (curry ΔΣ⊔ Σ) (collapse-ΔΣs Σ ΔΣs₀) (map (curry collapse-ΔΣs Σ) ΔΣs*))]))

  (: collapse-R : Σ R → (Option (Pairof W^ ΔΣ)))
  ;; Collapse result into:
  ;; - Answers grouped by arities
  ;; - Collapsed store-delta
  (define (collapse-R Σ R)
    (define retain?
      (for*/fold ([m : (HashTable Integer (HashTable Integer (Option (U T -prim)))) (hasheq)])
                 ([W (in-hash-keys R)]
                  [n (in-value (length W))]
                  [(Vᵢ i) (in-indexed W)])
        ((inst hash-update Integer (HashTable Integer (Option (U T -prim))))
         m n
         (λ (m*)
           (cond [(set? Vᵢ) (hash-set m* i #f)]
                 [(not (hash-has-key? m* i)) (hash-set m* i Vᵢ)]
                 [(equal? (hash-ref m* i) Vᵢ) m*]
                 [else (hash-set m* i #f)]))
         hasheq)))

    (define (Ws^) : W^
      (define m
        (for*/fold ([m : (HashTable Integer (HashTable Integer D)) (hasheq)])
                   ([(W ΔΣs) (in-hash R)]
                    [n (in-value (length W))]
                    [ΔΣ* (in-value (collapse-ΔΣs Σ ΔΣs))]
                    [ΔΓ* (in-value (cdr ΔΣ*))]
                    [(Dᵢ i) (in-indexed W)])
          (define Σ* (⧺ Σ ΔΣ*))
          ((inst hash-update Integer (HashTable Integer D))
           m n
           (λ (m*)
             (cond
               [(hash-ref (hash-ref retain? n) i)
                (assert (and (not (set? Dᵢ))
                             (equal? Dᵢ (hash-ref (hash-ref retain? n) i))))
                (hash-set m* i Dᵢ)]
               [else
                (hash-update m* i (λ ([D₀ : D]) (V⊔ (assert D₀ set?) (unpack Dᵢ Σ*))) mk-∅)]))
           hasheq)))
      (define Ws
        (for/set: : W^ ([(n m*) (in-hash m)])
          (for/list : W ([i (in-range (hash-count m*))])
            (hash-ref m* i))))
      ;; HACK
      (if (hash-has-key? R '()) (set-add Ws '()) Ws))

    (and (not (hash-empty? R))
         (let ([ΔΣ* (match-let ([(cons ΔΣ₀^ ΔΣ^*) (map (curry collapse-ΔΣs Σ) (hash-values R))])
                      (foldl (curry ΔΣ⊔ Σ) ΔΣ₀^ ΔΣ^*))])
           (cons (Ws^) ΔΣ*))))

  (: R⊔ : R R → R)
  (define (R⊔ R₁ R₂)
    (: compact : (℘ ΔΣ) (℘ ΔΣ) → (℘ ΔΣ))
    (define (compact ΔΣs₁ ΔΣs₂)
      (if (> (set-count ΔΣs₁) (set-count ΔΣs₂))
          (set-fold ΔΣ⊔₁ ΔΣs₁ ΔΣs₂)
          (set-fold ΔΣ⊔₁ ΔΣs₂ ΔΣs₁)))
    ((inst hash-union W (℘ ΔΣ)) R₁ R₂ #:combine compact))

  (: group-by-ans : Σ R → R)
  ;; Colllapse redundant store deltas
  (define (group-by-ans Σ r)
    (for/hash : R ([(W ΔΣs) (in-hash r)])
      ;; Partition store-deltas by "absolute" answers
      (define ΔΣs* (ΔΣs . partition-by . (λ ([ΔΣ : ΔΣ]) (unpack-W W (⧺ Σ ΔΣ)))))
      ;; Partition further by some heuristic notion of "path invariant" before collapsing
      (define ΔΣs**
        (for/union : (℘ ΔΣ) ([ΔΣs (in-hash-values ΔΣs*)])
          (precise-collapse-ΔΣs Σ ΔΣs)))
      (values W ΔΣs**)))

  (: precise-collapse-ΔΣs : Σ (℘ ΔΣ) → (℘ ΔΣ))
  ;; Collapse store-deltas with full store as context, so can collapse many symbolic expressions
  (define (precise-collapse-ΔΣs Σ ΔΣs)
    ;; Compute largest common path-condition domain
    (define shared-dom
      (for/fold ([acc : (℘ T) (dom (cdr (set-first ΔΣs)))])
                ([ΔΣ : ΔΣ (in-set (set-rest ΔΣs))])
        (∩ acc (dom (cdr ΔΣ)))))
    (: restrict : ΔΣ → ΔΣ)
    (define (restrict ΔΣ₀)
      (define Σ* (⧺ Σ ΔΣ₀))
      (match-define (cons ΔΞ₀ ΔΓ₀) ΔΣ₀)
      (cons ΔΞ₀
            (for/fold ([acc : ΔΓ ΔΓ₀])
                      ([(T D) (in-hash ΔΓ₀)] #:unless (∋ shared-dom T))
              (hash-set acc T (if (or (-prim? D) (set? D)) D (unpack T Σ*))))))
    (define partitions
      (ΔΣs
       . partition-by .
       (λ ([ΔΣ : ΔΣ])
         (for*/hash : (HashTable T Base) ([(T D) (in-hash (cdr ΔΣ))]
                                          #:when (∋ shared-dom T)
                                          #:when (prop? T D))
           (values T (-b-unboxed (assert (if (set? D) (set-first D) D) -b?)))))))
    (for/set: : (℘ ΔΣ) ([ΔΣs : (℘ ΔΣ) (in-hash-values partitions)])
      (collapse-ΔΣs Σ (map/set restrict ΔΣs))))

  (: partition-by (∀ (X Y) (℘ X) (X → Y) → (Immutable-HashTable Y (℘ X))))
  (define (partition-by xs f)
    (for/fold ([m : (Immutable-HashTable Y (℘ X)) (hash)])
              ([x (in-set xs)])
      (hash-update m (f x) (λ ([xs : (℘ X)]) (set-add xs x)) mk-∅)))

  (: map-R:ΔΣ : (ΔΣ → ΔΣ) R → R)
  (define (map-R:ΔΣ f R₀)
    (for/hash : R ([(W ΔΣs) (in-hash R₀)])
      (values W (map/set f ΔΣs))))
)
