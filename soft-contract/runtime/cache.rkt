#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
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

  (: R-of ([(U V V^ W)] [ΔΣ] . ->* . R))
  (define (R-of V [ΔΣ ⊥ΔΣ])
    (define (with [A : W]) (hash A {set ΔΣ}))
    (cond [(list? V) (with V)]
          [(set? V) (if (set-empty? V) ⊥R (with (list V)))]
          [else (with (list {set V}))]))

  (: ΔΣ⧺R : ΔΣ R → R)
  (define (ΔΣ⧺R ΔΣ R)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ ΔΣ₀)) R)]))

  (: R⧺ΔΣ : R ΔΣ → R)
  (define (R⧺ΔΣ R ΔΣ)
    (cond [(and (hash-empty? (car ΔΣ)) (hash-empty? (cdr ΔΣ))) R]
          [else (map-R:ΔΣ (λ (ΔΣ₀) (⧺ ΔΣ₀ ΔΣ)) R)])) 

  (: collapse-R/ΔΣ : R → (Option ΔΣ))
  (define (collapse-R/ΔΣ R)
    (match (hash-values R)
      ['() #f]
      [(cons ΔΣs₀ ΔΣs*) (foldl ΔΣ⊔ (collapse-ΔΣs ΔΣs₀) (map collapse-ΔΣs ΔΣs*))]))

  (: collapse-R : R → (Option (Pairof W^ ΔΣ)))
  ;; FIXME fix return type to `W`
  (define (collapse-R R)
    ;; FIXME rewrite the mess below with vectors
    (define erase?
      (let ([m (for*/fold ([m : (HashTable Integer (HashTable Integer V^)) (hasheq)])
                          ([W (in-hash-keys R)]
                           [n (in-value (length W))]
                           [(Vᵢ i) (in-indexed W)])
                 ((inst hash-update Integer (HashTable Integer V^))
                  m n
                  (λ ([m* : (HashTable Integer V^)])
                    (hash-update m* i (λ ([Vs₀ : V^]) (∪ Vs₀ Vᵢ)) mk-∅))
                  (λ () (hasheq))))])
        (for/hasheq : (HashTable Integer (HashTable Integer Boolean)) ([(n m*) (in-hash m)])
          (values n (for/hasheq : (HashTable Integer Boolean) ([(i Vᵢ) (in-hash m*)])
                      (values i (> (set-count Vᵢ) 1)))))))

    (define (Ws^) : W^
      (define m
        (for*/fold ([m : (HashTable Integer (HashTable Integer V^)) (hasheq)])
                   ([(W ΔΣs) (in-hash R)]
                    [n (in-value (length W))]
                    [ΔΣ* (in-value (collapse-ΔΣs ΔΣs))]
                    [ΔΓ* (in-value (cdr ΔΣ*))]
                    [(Vᵢ i) (in-indexed W)])
          (: span₁ : V V^ → V^)
          (define (span₁ V acc)
            (cond [(not (T? V)) (V⊔₁ V acc)]
                  [(hash-has-key? ΔΓ* V)
                   (set-fold span₁ acc (assert (hash-ref ΔΓ* V) set?))]
                  [else (set-add acc V)]))
          (define (span [Vs : V^]) (set-fold span₁ ∅ Vs))
          ((inst hash-update Integer (HashTable Integer V^))
           m n
           (λ ([m* : (HashTable Integer V^)])
             (hash-update
              m* i
              (λ ([V₀ : V^])
                (define Vᵢ* (if (hash-ref (hash-ref erase? n) i) (span Vᵢ) Vᵢ))
                (if (set-empty? V₀) Vᵢ* (V⊔ V₀ Vᵢ*)))
              mk-∅))
           (λ () (hasheq)))))
      (define Ws
        (for/set: : W^ ([(n m*) (in-hash m)])
          (for/list : W ([i (in-range (hash-count m*))])
            (hash-ref m* i))))
      ;; HACK
      (if (hash-has-key? R '()) (set-add Ws '()) Ws))

    (and (not (hash-empty? R))
         (let ([ΔΣ* (match-let ([(cons ΔΣ₀^ ΔΣ^*) (map collapse-ΔΣs (hash-values R))])
                      (foldl ΔΣ⊔ ΔΣ₀^ ΔΣ^*))])
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
  ;; Parition store-deltas by (absolute) return values then collapse
  (define (group-by-ans Σ r)
    (define m
      (for*/fold ([acc : (HashTable W (HashTable W (℘ ΔΣ))) (hash)])
                 ([(Wᵢ ΔΣsᵢ) (in-hash r)]
                  [ΔΣᵢ : ΔΣ(in-set ΔΣsᵢ)])
        (define Σ* (⧺ Σ ΔΣᵢ))
        (define Wᵢ:unpacked (unpack-W Wᵢ Σ*))
        ((inst hash-update W (HashTable W (℘ ΔΣ)))
         acc Wᵢ
         (λ ([h : (HashTable W (℘ ΔΣ))])
           (hash-update h Wᵢ:unpacked (λ ([ΔΣs : (℘ ΔΣ)]) (set-add ΔΣs ΔΣᵢ)) mk-∅))
         (λ () (hash)))))
    (for/hash : R ([(W h) (in-hash m)])
      (values W (for/set: : (℘ ΔΣ) ([ΔΣs (in-hash-values h)])
                  (collapse-ΔΣs ΔΣs)))))

  (: map-R:ΔΣ : (ΔΣ → ΔΣ) R → R)
  (define (map-R:ΔΣ f R₀)
    (for/hash : R ([(W ΔΣs) (in-hash R₀)])
      (values W (map/set f ΔΣs))))
)
