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
  (init-depend val^)

  (define ⊤Ψ : Ψ (hash))
  (define ⊤Φ (Φ (hasheq) ⊤Ψ))
  (define ⊥Φ^ {set ⊤Φ})

  (: Ψ@ : (U Φ Φ^ Ψ) (Listof T) → (℘ P))
  (define (Ψ@ x Ts)
    (define (go [Ψ : Ψ]) (hash-ref Ψ Ts mk-∅))
    (define (go-Φ [Φ : Φ]) (go (Φ-condition Φ)))
    (cond [(set? x) (for/fold ([acc : (℘ P) (go-Φ (set-first x))])
                               ([Φᵢ (in-set (set-rest x))])
                       (∩ acc (go-Φ Φᵢ)))]
          [(Φ? x) (go-Φ x)]
          [else (go x)]))

  (: $@ : Φ α → S)
  (define ($@ Φ α)
    (hash-ref (Φ-alias Φ) α (λ () (error '$@ "nothing at ~a" (show-α α)))))

  (: $@* : Φ^ α → R^)
  (define ($@* Φs α)
    (define m
      (for/fold ([m : (HashTable W Φ^) (hash)]) ([Φ (in-set Φs)])
        (hash-update m (list ($@ Φ α)) (λ ([Φs : Φ^]) (Φ^⊔ Φs Φ)) mk-∅)))
    (list->set (hash-map m R)))

  (: Ψ+ (case-> [Ψ (U P (℘ P)) (Listof S) → Ψ]
                [Φ (U P (℘ P)) (Listof S) → Φ]
                [Φ^ (U P (℘ P)) (Listof S) → Φ^]))
  (define (Ψ+ x p* xs)
    (define go : (Ψ → Ψ)
      (if (set? p*)
          (λ (Ψ₀) (hash-update Ψ₀ xs (λ ([ps : (℘ P)]) (∪ ps p*)) mk-∅))
          (λ (Ψ₀) (hash-update Ψ₀ xs (λ ([ps : (℘ P)]) (set-add ps p*)) mk-∅))))
    (define go-Φ : (Φ → Φ) (match-lambda [(Φ $ Ψ) (Φ $ (go Ψ))]))
    (cond [(set? x) (map/set go-Φ x)]
          [(Φ? x) (go-Φ x)]
          [else (go x)]))

  (: $+ (case-> [Φ α S → Φ]
                [Φ^ α S → Φ^]))
  (define ($+ Φ* α S) ((lift-Φ* (match-lambda [(Φ $ Ψ) (Φ (hash-set $ α S) Ψ)])) Φ*)) 

  (: collapse-R^ : R^ → (Values W^ Φ^))
  (define (collapse-R^ R^)
    (for/fold ([W^ : W^ ∅] [Φ^ : Φ^ ∅]) ([R* (in-set R^)])
      (match-define (R W* Φ^*) R*)
      (values (set-add W^ W*) ((iter-⊔ Φ^⊔) Φ^ Φ^*))))

  (: collapse-R^/Φ^ : R^ → Φ^)
  (define (collapse-R^/Φ^ R^) (foldl (iter-⊔ Φ^⊔) ∅ (set-map R^ R-_1)))

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

  #;(: R^⊔ : R^ R^ → R^)
  #;(define (R^⊔ R^₁ R^₂)
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

  #;(: Φ^⊔ : Φ^ Φ^ → Φ^)
  #;(define (Φ^⊔ Φ^₁ Φ^₂)
    (for/fold ([acc : Φ^ Φ^₁]) ([Φ (in-set Φ^₂)])
      (Φ^+ acc Φ))) 

  #;(: Φ^+ : Φ^ Φ → Φ^)
  #;(define (Φ^+ Φ^ Φᵢ)
    (match-define (Φ $ᵢ Ψᵢ) Φᵢ)

    (: $⊔ : $ $ → $)
    (define ($⊔ $₁ $₂)
      (for*/fold ([acc : $ $₁])
                 ([(α S₁) (in-hash $₁)]
                  [S₂ (in-value (hash-ref $₂ α))]
                  #:unless (equal? S₁ S₂))
        (hash-set acc α (S:α α))))

    (: Ψ⊔ : Ψ Ψ → Ψ)
    (define (Ψ⊔ Ψ₁ Ψ₂)
      (for*/fold ([acc : Ψ Ψ₁])
                 ([(args Ps₁) (in-hash Ψ₁)]
                  [Ps₂ (in-value (Ψ@ Ψ₂ args))]
                  #:unless (equal? Ps₁ Ps₂)
                  [Ps* (in-value (∩ Ps₁ Ps₂))])
        (if (set-empty? Ps*)
            (hash-remove acc args)
            (hash-set acc args Ps*))))
    
    (: $-compat? : $ → Boolean)
    (define ($-compat? $₀)
      (for/and ([(α S₀) (in-hash $₀)])
        (define Sᵢ (hash-ref $ᵢ α))
        (or (equal? Sᵢ S₀)
            (let ([S^ (S:α α)])
              (or (equal? Sᵢ S^) (equal? S₀ S^))))))

    (: Ψ-compat? : Ψ → Boolean)
    (define (Ψ-compat? Ψ₀)
      (for/and ([(args Psᵢ) (in-hash Ψᵢ)])
        (define Ps₀ (Ψ@ Ψ₀ args))
        (or (⊆ Psᵢ Ps₀) (⊆ Ps₀ Psᵢ))))

    (define compat? : (Φ → Boolean)
      (match-lambda [(Φ $₀ Ψ₀) (Ψ-compat? Ψ₀) ($-compat? $₀)]))
    
    (define Φ₀s (set-filter compat? Φ^))
    (define-values ($* Ψ*)
      (for/fold ([$* : $ $ᵢ] [Ψ* : Ψ Ψᵢ])
                ([Φ₀ (in-set Φ₀s)])
        (match-define (Φ $₀ Ψ₀) Φ₀)
        (values ($⊔ $* $₀) (Ψ⊔ Ψ* Ψ₀))))
    (set-add (set-subtract Φ^ Φ₀s) (Φ $* Ψᵢ)))

  (: Ψ↓ : Ψ (℘ α) → Ψ)
  (define (Ψ↓ Ψ₀ αs)
    (for/fold ([Ψ : Ψ Ψ₀]) ([args (in-hash-keys Ψ₀)]
                            #:unless (for/and : Boolean ([S (in-list args)])
                                       (in-scope? S αs)))
      (hash-remove Ψ args)))

  (: $↓ : $ (℘ α) → $)
  (define ($↓ $₀ αs)
    (for/fold ([$ : $ $₀]) ([(α S) (in-hash $₀)]
                            #:unless (∋ αs α)
                            #:unless (in-scope? S αs))
      (hash-remove $ α)))

  (: Φ↓ (case-> [Φ (℘ α) → Φ]
                [Φ^ (℘ α) → Φ^]))
  (define (Φ↓ Φ* αs)
    ((lift-Φ* (match-lambda [(Φ $ Ψ) (Φ ($↓ $ αs) (Ψ↓ Ψ αs))])) Φ*))

  (: lift-Φ* : (Φ → Φ) → (case-> [Φ → Φ] [Φ^ → Φ^]))
  (define ((lift-Φ* go) Φ*) (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (define $⊔ : (Joiner $)
    (λ ($₁ $₂)
      (assert (= (hash-count $₁) (hash-count $₂)))
      (for/fold ([$ : (Option $) $₁])
                ([(α S₁) (in-hash $₁)] #:break (not $))
        (define S₂ (hash-ref $₂ α))
        (or (and (equal? S₁ S₂) $)
            (let ([S* (S:α α)])
              (and (equal? S₁ S*) $)
              (and (equal? S₂ S*) (hash-set (assert $) α S₂)))))))

  (define Ψ⊔ : (Joiner Ψ)
    (λ (Ψ₁ Ψ₂)
      (for/fold ([Ψ : (Option Ψ) Ψ₁])
                ([(args Ps₁) (in-hash Ψ₁)] #:break (not Ψ))
        (define Ps₂ (Ψ@ Ψ₂ args))
        (or (and (⊆ Ps₁ Ps₂) Ψ)
            (and (⊆ Ps₂ Ps₁) (hash-set (assert Ψ) args Ps₂))))))

  (define Φ⊔ : (Joiner Φ)
    (match-lambda**
     [((Φ $₁ Ψ₁) (Φ $₂ Ψ₂))
      (with-guard ([$ ($⊔ $₁ $₂)]
                   [Ψ (Ψ⊔ Ψ₁ Ψ₂)])
        (Φ $ Ψ))]))

  (define R⊔ : (Joiner R)
    (match-lambda**
     [((R W₁ Φ^₁) (R W₂ Φ^₂))
      (with-guard ([Φ^* ((iter-⊔ Φ^⊔) Φ^₁ Φ^₂)])
        (define T⊔/Φ^ : (Joiner T^)
          (match-lambda**
           [(x x) x]
           [((? S? S₁) (and S₂ (S:α α)))
            #:when (for/and : Boolean ([Φ₁ (in-set Φ^₁)])
                     (equal? (hash-ref (Φ-alias Φ₁) α) S₁))
            S₂]
           [((and S₁ (S:α α)) (? S? S₂))
            #:when (for/and : Boolean ([Φ₂ (in-set Φ^₂)])
                     (equal? (hash-ref (Φ-alias Φ₂) α) S₂))
            S₁]
           [((? V? V) (? set? V^)) #:when (∋ V^ V) V^]
           [((? set? V^) (? V? V)) #:when (∋ V^ V) V^]
           [(_ _) #f]))
        (with-guard ([W (?map T⊔/Φ^ W₁ W₂)])
          (R W Φ^*)))]))

  (define Φ^⊔ (compact-with Φ⊔))
  (define R^⊔ (compact-with R⊔))
  )
