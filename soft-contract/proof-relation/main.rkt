#lang typed/racket/base

(provide prover@)

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/list
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
  (import val^ evl^
          sat-result^ (prefix l: local-prover-core^) (prefix x: ext-prover-core^))
  (export prover^)
  (init-depend local-prover-core^)

  (: split-results ([Σ (U R R^)] [V #:fast? Boolean] . ->* . (Values R^ R^)))
  (define (split-results Σ R₀ [P 'values] #:fast? [fast? #f])
    (define-values (R✓ R✗ R?) (partition-results Σ R₀ P #:fast? fast?))
    (for/fold ([R✓* : R^ R✓] [R✗* : R^ R✗]) ([R (in-set R?)])
      (values (set-add R✓* (l:∧  R P))
              (set-add R✗* (l:∧¬ R P)))))

  (: partition-results ([Σ (U R R^)] [V #:fast? Boolean] . ->* . (Values R^ R^ R^)))
  (define (partition-results Σ R₀ [P 'values] #:fast? [fast? #f])
    (: go (case-> [R  → (Values ?R ?R ?R)]
                  [R^ → (Values R^ R^ R^)]))
    (define (go R)
      (cond
        [(R? R)
         (define-values (R✓ R✗ R?) (with-checker l:check Σ P R))
         (define ?R* (validate-R R?))
         (define-values (R✓* R✗* R?*)
           (if (and (not fast?) ?R*)
               (let-values ([(R✓* R✗* R?*) (with-checker x:check Σ P ?R*)])
                 (values (R⊔ R✓ R✓*) (R⊔ R✗ R✗*) R?*))
               (values R✓ R✗ ?R*)))
         (values (validate-R R✓*) (validate-R R✗*) (validate-R R?*))]
        [else
         (define (⊕ [R^ : R^] [?R : ?R]) (if ?R (set-add R^ ?R) R^))
         (for/fold ([R✓ : R^ ∅] [R✗ : R^ ∅] [R? : R^ ∅])
                   ([Rᵢ (in-set R)])
           (define-values (R✓* R✗* R?*) (go Rᵢ))
           (values (⊕ R✓ R✓*) (⊕ R✗ R✗*) (⊕ R? R?*)))]))
    (if (set? R₀)
        (go R₀)
        (let-values ([(R✓ R✗ R?) (go R₀)])
          (values (inj-R R✓) (inj-R R✗) (inj-R R?)))))

  (: check-plausible-index ([Σ (U R R^) Natural] [#:fast? Boolean] . ->* . (Values R^ R^)))
  (define (check-plausible-index Σ Rᵥ i #:fast? [fast? #f])
     ???)
  #;(: check-plausible-index ([Σ Φ^ V^ Natural] [Boolean] . ->* . (Values Φ^ Φ^)))
  #;(define (check-plausible-index Σ Φ^ V^ i [fast? #f])
    (plausible-splits Σ Φ^ '= (list V^ {set (-b i)}))) 

  (define V-arity l:V-arity) 

  (: inj-R : ?R → R^)
  (define (inj-R R)
    (cond [(and R (validate-R R)) => set]
          [else ∅]))

  (: with-checker : (Σ Φ V (Listof V) → ?Dec) Σ V R → (Values R R R))
  (define (with-checker check Σ P R₀)
    (match-define (R W₀ Φ^₀) R₀)
    (define ⊥R (R (make-list (length W₀) ∅) ∅))
    (for*/fold ([R✓ : R ⊥R] [R✗ : R ⊥R] [R? : R ⊥R])
               ([Vs (in-list (cartesian W₀))] [Φ : Φ (in-set Φ^₀)])
      (case (check Σ Φ P Vs)
        [(✓)  (values (R⊔₁ R✓ Vs Φ) R✗ R?)]
        [(✗)  (values R✓ (R⊔₁ R✗ Vs Φ) R?)]
        [else (values R✓ R✗ (R⊔₁ R? Vs Φ))])))
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
  )
|#
