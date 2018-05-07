#lang typed/racket/base

(provide evl@)

(require (except-in racket/set for/set for/seteq for*/set for*/seteq)
         racket/match
         racket/splicing
         typed/racket/unit
         typed-racket-hacks
         set-extras
         unreachable
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit evl@
  (import val^ pretty-print^)
  (export evl^)

  (define ⊤Φ (Φ (hasheq) (hash)))
  (define ⊥Φ^ {set ⊤Φ})

  (: Ψ@ : Φ (Listof T) → (℘ P))
  (define (Ψ@ Φ Ts) (hash-ref (Φ-condition Φ) Ts mk-∅))

  (: $@ : Φ α → S)
  (define ($@ Φ α)
    (hash-ref (Φ-alias Φ) α (λ () (error '$@ "nothing at ~a" (show-α α)))))

  (: $@* : Φ^ α → R^)
  (define ($@* Φ^ α) (partition-Φ^ (λ (Φ) (list ($@ Φ α))) Φ^))

  (: $+ (case-> [Φ α (U T T^) → Φ]
                [Φ^ α (U T T^) → Φ^]))
  (define ($+ Φ* α T^)
    (define go : (Φ → Φ)
      (let ([S (if (S? T^) T^ (S:α α))])
        (match-lambda [(Φ $ Ψ) (Φ (hash-set $ α S) Ψ)])))
    (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (: $+* (case-> [Φ (Listof α) (Listof (U T T^)) → Φ]
                 [Φ^ (Listof α) (Listof (U T T^)) → Φ^]))
  (define ($+* Φ* αs Ts)
    (define go : (Φ → Φ)
      (let ([Ss : (Listof S) (for/list ([α (in-list αs)] [T (in-list Ts)])
                               (if (S? T) T (S:α α)))])
        (match-lambda [(Φ $₀ Ψ)
                       (Φ (for/fold ([$ : $ $₀])
                                    ([α (in-list αs)] [S (in-list Ss)])
                            (hash-set $ α S))
                          Ψ)])))
    (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (: partition-Φ^ : (Φ → W) Φ^ → R^)
  (define (partition-Φ^ f Φs)
    (define m (for/fold ([m : (HashTable W Φ^) (hash)])
                        ([Φ (in-set Φs)])
                (hash-update m (f Φ) (λ ([Φs : Φ^]) (set-add Φs Φ)) mk-∅)))
    (list->set (hash-map m R)))

  (: collapse-R^ : R^ → (Values W^ Φ^))
  (define (collapse-R^ R^)
    (for/fold ([W^ : W^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R W* Φ^*) R*)
      (values (set-add W^ W*) (∪ Φ^ Φ^*))))

  (: collapse-R^/Φ^ : R^ → Φ^)
  (define (collapse-R^/Φ^ R^) (set-union-map R-_1 R^))

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
  )
