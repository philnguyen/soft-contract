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

  (: Ψ↓ : Ψ (℘ α) → Ψ)
  (define (Ψ↓ Ψ₀ αs)
    (for/fold ([Ψ : Ψ Ψ₀]) ([args (in-hash-keys Ψ₀)]
                            #:unless (for/and : Boolean ([S (in-list args)])
                                       (in-scope? S αs)))
      (hash-remove Ψ args)))

  (: $↓ : $ (℘ α) → $)
  (define ($↓ $₀ αs)
    (for/fold ([$ : $ $₀]) ([(α S) (in-hash $₀)])
      (cond [(not (in-scope? α αs)) (hash-remove $ α)]
            [(not (in-scope? S αs)) (hash-set $ α (S:α α))]
            [else $])))

  (: Φ↓ (case-> [Φ (℘ α) → Φ]
                [Φ^ (℘ α) → Φ^]))
  (define (Φ↓ Φ* αs)
    ((lift-Φ* (match-lambda [(Φ $ Ψ) (Φ ($↓ $ αs) (Ψ↓ Ψ αs))])) Φ*))

  (: lift-Φ* : (Φ → Φ) → (case-> [Φ → Φ] [Φ^ → Φ^]))
  (define ((lift-Φ* go) Φ*) (if (set? Φ*) (map/set go Φ*) (go Φ*)))

  (define cmp-$ : (?Cmp $)
    (λ ($₁ $₂)
      (for/fold ([cmp : ?Ord '=])
                ([(α S₁) (in-hash $₁)] #:break (not cmp))
        (match* (S₁ (hash-ref $₂ α))
          [(S S) cmp]
          [((S:α (== α)) _) (concat-ord (assert cmp) '>)]
          [(_ (S:α (== α))) (concat-ord (assert cmp) '<)]
          [(_ _) #f]))))

  (define cmp-Ψ : (?Cmp Ψ)
    (λ (Ψ₁ Ψ₂)
      (define-values (cmp₁ Ψ₂:rest)
        (for/fold ([cmp : ?Ord '=] [Ψ₂:rest : Ψ Ψ₂])
                  ([(args Ps₁) (in-hash Ψ₁)] #:break (not cmp))
          (values (concat-ord (assert cmp) (cmp-sets (Ψ@ Ψ₂:rest args) Ps₁))
                  (hash-remove Ψ₂:rest args))))
      (and cmp₁
           (if (hash-empty? Ψ₂:rest)
               cmp₁
               (concat-ord cmp₁ '>)))))

  (define cmp-Φ : (?Cmp Φ)
    (match-lambda**
     [((Φ $₁ Ψ₁) (Φ $₂ Ψ₂)) (Ord:* (cmp-$ $₁ $₂) (cmp-Ψ Ψ₁ Ψ₂))]))

  (define cmp-Φ^ (set-lift-cmp cmp-Φ))

  (: cmp-T^/$ : (Option (℘ $)) (Option (℘ $)) → (?Cmp T^))
  (define (cmp-T^/$ $^₁ $^₂)
    (define simpl : (?Cmp T^)
      (match-lambda**
       ;; cache-independent
       [(x x) '=]
       [((? set? V^₁) (? set? V^₂)) (cmp-sets V^₁ V^₂)]
       [((? V? V) (? set? V^)) #:when (∋ V^ V) '<]
       [((? set? V^) (? V? V)) #:when (∋ V^ V) '>]
       [(_ _) #f]))
    (if (and $^₁ $^₂)
        (match-lambda**
         [((? S? S₁) (and S₂ (S:α α)))
          #:when (for/and : Boolean ([$₁ (in-set $^₁)])
                   (equal? (hash-ref $₁ α) S₁))
          '<]
         [((and S₁ (S:α α)) (? S? S₂))
          #:when (for/and : Boolean ([$₂ (in-set $^₂)])
                   (equal? (hash-ref $₂ α) S₂))
          '>]
         [(T₁ T₂) (simpl T₁ T₂)])
        simpl))

  (define cmp-R : (?Cmp R)
    (match-lambda**
     [((R W₁ Φ^₁) (R W₂ Φ^₂)) #:when (= (length W₁) (length W₂))
      (define cmp-T^ (cmp-T^/$ (map/set Φ-alias Φ^₁) (map/set Φ-alias Φ^₂)))
      (define W₁-vs-W₂ (foldl (λ ([T₁ : T^] [T₂ : T^] [o : ?Ord])
                                (and o (concat-ord o (cmp-T^ T₁ T₂))))
                              '= W₁ W₂))
      (Ord:* W₁-vs-W₂ (cmp-Φ^ Φ^₁ Φ^₂))]
     [(_ _) #f])) 

  (define Φ^⊔ (compact-with ((inst join-by-max Φ) cmp-Φ)))
  (define R^⊔ (compact-with ((inst join-by-max R) cmp-R)))
  )
