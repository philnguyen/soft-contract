#lang typed/racket/base

(provide evl@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         racket/splicing
         typed/racket/unit
         typed-racket-hacks
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit evl@
  (import val^ pretty-print^)
  (export evl^)

  (define ⊤Φ (Φ (hasheq) (hash)))
  (define ⊥Φ^ {set ⊤Φ})

  (: Ψ@ : (U Φ Φ^) (Listof T) → (℘ P))
  (define (Ψ@ Φ* Ts)
    (define (go [Φ : Φ]) (hash-ref (Φ-condition Φ) Ts mk-∅))
    (if (set? Φ*)
        (for/fold ([acc : (℘ P) (go (set-first Φ*))])
                  ([Φᵢ (in-set (set-rest Φ*))])
          (∩ acc (go Φᵢ)))
        (go Φ*)))

  (: $@ : Φ α → S)
  (define ($@ Φ α)
    (hash-ref (Φ-alias Φ) α (λ () (error '$@ "nothing at ~a" (show-α α)))))

  (: $@* : Φ^ α → R^)
  (define ($@* Φ^ α) (partition-Φ^ (λ (Φ) (list ($@ Φ α))) Φ^))

  (: Ψ+ (case-> [Φ P (Listof S) → Φ]
                [Φ^ P (Listof S) → Φ^]))
  (define (Ψ+ Φ* p xs)
    (define go : (Φ → Φ)
      (match-lambda
        [(Φ $ Ψ₀)
         (Φ $ (hash-update Ψ₀ xs (λ ([ps : (℘ P)]) (set-add ps p)) mk-∅))]))
    (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (: $+ (case-> [Φ α S → Φ]
                [Φ^ α S → Φ^]))
  (define ($+ Φ* α S)
    (define go : (Φ → Φ) (match-lambda [(Φ $ Ψ) (Φ (hash-set $ α S) Ψ)]))
    (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (: partition-Φ^ : (Φ → W) Φ^ → R^)
  (define (partition-Φ^ f Φs)
    (define m (for/fold ([m : (HashTable W Φ^) (hash)])
                        ([Φ (in-set Φs)])
                (hash-update m (f Φ) (λ ([Φs : Φ^]) (Φ^+ Φs Φ)) mk-∅)))
    (list->set (hash-map m R)))

  (: collapse-R^ : R^ → (Values W^ Φ^))
  (define (collapse-R^ R^)
    (for/fold ([W^ : W^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R W* Φ^*) R*)
      (values (set-add W^ W*) (Φ^⊔ Φ^ Φ^*))))

  (: collapse-R^/Φ^ : R^ → Φ^)
  (define (collapse-R^/Φ^ R^) (foldl Φ^⊔ ∅ (set-map R^ R-_1)))

  (: collapse-R^/W^ : R^ → W^)
  (define (collapse-R^/W^ R^) (map/set R-_0 R^))

  (splicing-local
      ((: with-collapse (∀ (X) (Φ^ → (℘ X)) → R^ → (℘ X)))
       (define ((with-collapse on-Φ^) R^) (on-Φ^ (collapse-R^/Φ^ R^))))
    (: with-2-paths/collapse : (∀ (X) (→ (Values R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
    (define (with-2-paths/collapse mk on-t on-f)
      (with-2-paths mk (with-collapse on-t) (with-collapse on-f)))
    (: with-3-paths/collapse : (∀ (X) (→ (Values R^ R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
    (define (with-3-paths/collapse mk f₁ f₂ f₃)
      (with-3-paths mk (with-collapse f₁) (with-collapse f₂) (with-collapse f₃))))

  (: T->R : (U T T^) Φ^ → R)
  (define (T->R x Φ^)
    (define W (if (or (set? x) (S? x)) (list x) (list (set x))))
    (R W Φ^))

  (: filter/arity : R^ Natural → (Values R^ W^))
  (define (filter/arity R^ n)
    (define-set others : W)
    (define-set R^-filtered : R)
    (for ([R* (in-set R^)])
      (match-define (R W* _) R*)
      (if (= n (length W*))
          (R^-filtered-add! R*)
          (others-add! W*)))
    (values R^-filtered others)) 

  (: with-2-paths (∀ (X) (→ (Values R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X)))
  (define (with-2-paths mk on-t on-f)
    (define-values (R^₁ R^₂) (mk))
    (∪ (if (set-empty? R^₁) ∅ (on-t R^₁))
       (if (set-empty? R^₂) ∅ (on-f R^₂))))

  (: with-3-paths (∀ (X) (→ (Values R^ R^ R^)) (R^ → (℘ X)) (R^ → (℘ X)) (R^ → (℘ X)) → (℘ X)))
  (define (with-3-paths mk f₁ f₂ f₃)
    (define-values (R^₁ R^₂ R^₃) (mk))
    (∪ (if (set-empty? R^₁) ∅ (f₁ R^₁))
       (if (set-empty? R^₂) ∅ (f₂ R^₂))
       (if (set-empty? R^₃) ∅ (f₃ R^₃))))

  (: R^⊔ : R^ R^ → R^)
  (define (R^⊔ R^₁ R^₂)
    (: go : R^ R → R^)
    (define (go R* Rᵢ)
      (match-define (R Wᵢ Φ^ᵢ) Rᵢ)
      (define subsumed? : (W → Boolean)
        (match Wᵢ
          [(list {singleton-set (? -b? b)})
           (λ (W₀) (or (equal? W₀ Wᵢ) (match? W₀ (list (== b)))))]
          [_ (λ (W₀) (equal? W₀ Wᵢ))]))
      
      (match (for/or : (Option R) ([R (in-set R*)] #:when (subsumed? (R-_0 R)))
               R)
        [(and R₀ (R _ Φ^₀)) (set-add (set-remove R* R₀) (R Wᵢ (Φ^⊔ Φ^₀ Φ^ᵢ)))]
        [_ (set-add R* Rᵢ)]))
    (for/fold ([acc : R^ R^₁]) ([R (in-set R^₂)])
      (go acc R)))

  (: Φ^⊔ : Φ^ Φ^ → Φ^)
  (define (Φ^⊔ Φ^₁ Φ^₂)
    (for/fold ([acc : Φ^ Φ^₁]) ([Φ (in-set Φ^₂)])
      (Φ^+ acc Φ)))

  (: Φ^+ : Φ^ Φ → Φ^)
  (define (Φ^+ Φ^ Φᵢ)
    (: $⊑ : $ $ → Boolean)
    (define ($⊑ $₁ $₂)
      (for/and ([(α S₁) (in-hash $₁)])
        (define S₂ (hash-ref $₂ α))
        (or (equal? S₁ S₂) (equal? S₂ (S:α α)))))
    
    (match-define (Φ $ᵢ Ψᵢ) Φᵢ)
    (define ?Φ₀ (for/or : (Option Φ) ([Φ₀ (in-set Φ^)])
                  (match-define (Φ $₀ Ψ₀) Φ₀)
                  (and (equal? Ψ₀ Ψᵢ) ($⊑ $₀ $ᵢ) Φ₀)))
    (set-add (if ?Φ₀ (set-remove Φ^ ?Φ₀) Φ^) Φᵢ))
  )
