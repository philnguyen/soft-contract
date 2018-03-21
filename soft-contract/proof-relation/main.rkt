#lang typed/racket/base

(provide prover@)

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/bool
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "sat-result.rkt"
         "local-prover-core.rkt"
         "ext-prover-core.rkt")

(define-unit prover-core@
  (import evl^ sat-result^ (prefix l: local-prover-core^) (prefix x: ext-prover-core^))
  (export prover^)
  (init-depend local-prover-core^)

  (: partition-sats ([Σ Φ^ V W] [#:fast? Boolean] . ->* . (Values Φ^ Φ^ Φ^)))
  (define (partition-sats Σ Φ^ P W #:fast? [fast? #f])
    (define-values (Φ^-✓ Φ^-✗ Φ^-?) (with-checker l:check Σ Φ^ P W))
    (if (or fast? (set-empty? Φ^-?))
        (values Φ^-✓ Φ^-✗ ∅)
        (let-values ([(Φ^-✓* Φ^-✗* Φ^-?*) (with-checker x:check Σ Φ^-? P W)])
          (values (∪ Φ^-✓ Φ^-✓*) (∪ Φ^-✗ Φ^-✗*) Φ^-?*))))

  (: plausible-splits (case-> [Σ R^ → (Values Φ^ Φ^)]
                              [Σ R^ Boolean → (Values Φ^ Φ^)]
                              [Σ Φ^ V W → (Values Φ^ Φ^)]
                              [Σ Φ^ V W Boolean → (Values Φ^ Φ^)]))
  (define plausible-splits
    (case-lambda
      [(Σ R^) (plausible-splits Σ R^ #f)]
      [(Σ R^ fast?)
       (for*/fold ([truish : Φ^ ∅] [falsish : Φ^ ∅])
                  ([Rᵢ (in-set R^)])
         (match-define (R Wᵢ Φ^ᵢ) Rᵢ)
         (define-values (Φ^₁ Φ^₂) (plausible-splits Σ Φ^ᵢ 'values Wᵢ fast?))
         (values (∪ truish Φ^₁) (∪ falsish Φ^₂)))]
      [(Σ Φ^ P W) (plausible-splits Σ Φ^ P W #f)]
      [(Σ Φ^ P W fast?)
       (define-values (Φ^-✓ Φ^-✗ Φ^-?) (partition-sats Σ Φ^ P W #:fast? fast?))
       (values (∪ Φ^-✓ (l:∧  Φ^-? P W))
               (∪ Φ^-✗ (l:∧¬ Φ^-? P W)))]))

  (: check-plausible-index ([Σ Φ^ V^ Natural] [Boolean] . ->* . (Values Φ^ Φ^)))
  (define (check-plausible-index Σ Φ^ V^ i [fast? #f])
    (plausible-splits Σ Φ^ '= (list V^ {set (-b i)})))

  (: with-checker : (Σ Φ V (Listof V) → ?Dec) Σ Φ^ V W → (Values Φ^ Φ^ Φ^))
  (define (with-checker check Σ Φ^₀ P W)
    (for/fold ([Φ^-✓ : Φ^ ∅] [Φ^-✗ : Φ^ ∅] [Φ^-? : Φ^ ∅])
              ([Φ : Φ (in-set Φ^₀)])
      (case (⊔* (λ ([Vs : (Listof V)]) (check Σ Φ P Vs)) (cartesian W))
        [(✓) (values (set-add Φ^-✓ Φ) Φ^-✗ Φ^-?)]
        [(✗) (values Φ^-✓ (set-add Φ^-✗ Φ) Φ^-?)]
        [else (values Φ^-✓ Φ^-✗ (set-add Φ^-? Φ))])))

  (define V-arity l:V-arity)
  )

(define-compound-unit/infer prover@
  (import static-info^ sto^ val^ evl^ prims^)
  (export prover^)
  (link sat-result@ local-prover-core@ ext-prover-core@ prover-core@))

#|
(define-unit pre-proof-system@
  (import static-info^ sat-result^ path^ pretty-print^
          (prefix local: local-prover^)
          (prefix ext: external-prover^))
  (export proof-system^)
  (init-depend local-prover^ external-prover^)

  (: p∋V : -σ -φ -h -V * → -R)
  (define (p∋V σ φ h . Vs)
    (match* (h Vs)
      [('values (list (-t.@ p xs))) (apply p∋V σ φ p xs)]
      [('not    (list (-t.@ p xs))) (not-R (apply p∋V σ φ p xs))]
      [(_ _)
       (match (apply local:p∋V σ φ h Vs)
         ['? (if (should-call-smt? (-φ-condition φ) h Vs)
                 (ext:p∋V (-φ-condition φ) h Vs)
                 '?)]
         [R R])]))

  (: V+ : -σ -φ -V^ (U -h -V) → -V^)
  (define (V+ σ φ V^ C)
    (define V₁+ : (-V (U -h -V) → -V)
      (match-lambda**
       [(V (-St/C _ 𝒾 _)) (V₁+ V (-st-p 𝒾))]
       [((-● ps) (? -h? h)) (-● (set-add ps h))]
       [(_ 'null?) -null]
       [(_ 'not) -ff]
       [(V _) V]))
    (for/fold ([acc : -V^ ∅]) ([V (in-set V^)])
      (case (V∈C σ φ {set V} C)
        [(✓) (set-add acc V)]
        [(✗) acc]
        [(?) (set-add acc (V₁+ V C))])))

  (: V- : -σ -φ -V^ (U -h -V) → -V^)
  (define (V- σ φ V^ C)
    (define V₁- : (-V (U -h -V) → -V)
      (match-lambda**
       [((-● ps) (? -h? h)) (-● (∪ (set-remove ps h)
                                   (if (-prim? h) {set (-not/c h)} ∅)))]
       [(V _) V]))
    (for/fold ([acc : -V^ V^])
              ([V (in-set V^)])
      (case (V∈C σ φ {set V} C)
        [(✓) (set-remove acc V)]
        [(✗) acc]
        [(?) (set-add (set-remove acc V) (V₁- V C))])))

  (: φ⊢t : -σ -φ -t → -R)
  (define (φ⊢t σ φ t)
    (cond [(hash-ref (-φ-condition φ) t #f) =>
           (λ ([ps : (℘ -h)]) (not-R (local:ps⇒p ps 'not)))]
          [else '?])) 

  
  )
|#
