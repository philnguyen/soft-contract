#lang typed/racket/base

(provide proof-system@)

(require racket/match
         racket/set
         racket/bool
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "widen.rkt"
         "ext.rkt"
         "local.rkt"
         )

(define-unit pre-proof-system@
  (import static-info^ sat-result^ path^ pretty-print^
          (prefix local: local-prover^)
          (prefix ext: external-prover^))
  (export proof-system^)
  (init-depend local-prover^ external-prover^)

  (define p⇒p local:p⇒p)

  (: V∈C : -σ -φ -V^ (U -h -V) → -R)
  ;; Check if value satisfies (flat) contract
  (define (V∈C σ φ V C)
    (if (-h? C) (p∋V^ σ φ C V) '?))

  (: φ+/-pV^ : -σ -φ -h -V^ * → (Values (℘ -φ) (℘ -φ)))
  (define (φ+/-pV^ σ φ h . V^s)
    (for/fold ([ts : (℘ -φ) ∅] [fs : (℘ -φ) ∅])
              ([Vs (in-set (cartesian V^s))])
      (case (apply p∋V σ φ h Vs)
        [(✓) (values (set-add ts φ) fs)]
        [(✗) (values ts (set-add fs φ))]
        [(?) (values (set-add ts (φ+pV  φ h Vs))
                     (set-add fs (φ+¬pV φ h Vs)))]))) 

  (: p∋V : -σ -φ -h -V * → -R)
  (define (p∋V σ φ h . Vs)
    (match (apply local:p∋V σ φ h Vs)
      ['? (if (should-call-smt? (-φ-condition φ) h Vs)
              (ext:p∋V (-φ-condition φ) h Vs)
              '?)]
      [R R]))

  (define p∋V^ (local:lift-p∋V p∋V))
  
  (: V+ : -σ -φ -V^ (U -h -V) → -V^)
  (define (V+ σ φ V^ C)
    (define V₁+ : (-V (U -h -V) → -V)
      (match-lambda**
       [(V (-St/C _ 𝒾 _)) (V₁+ V (-st-p 𝒾))]
       [((-● ps) (? -h? h)) (-● (set-add ps h))]
       [(V _) V]))
    (for/fold ([acc : -V^ ∅]) ([V (in-set V^)])
      (case (V∈C σ φ V^ C)
        [(✓) (set-add acc V)]
        [(✗) acc]
        [(?) (set-add acc (V₁+ V C))])))

  (: φ⊢t : -σ -φ -t → -R)
  (define (φ⊢t σ φ t)
    (cond [(hash-ref (-φ-condition φ) (list t) #f) =>
           (λ ([ps : (℘ -h)]) (not-R (local:ps⇒p ps 'not)))]
          [else '?])) 

  (: plausible-index? : -σ -φ -V^ Natural → Boolean)
  (define (plausible-index? σ φ V i)
    (case (apply p∋V^ σ φ '= (list V {set (-b i)}))
      [(✓ ?) #t]
      [else  #f]))

  (define V-arity local:V-arity)
  (define sat-one-of local:sat-one-of)

  (: φ+pV : -φ -h (Listof -V) → -φ)
  (define (φ+pV φ h Vs)
    (match-define (-φ Γ δσ) φ)
    (cond
      [(andmap -t? Vs)
       (match* (h Vs)
         [('values (list (-t.@ p xs))) ( φ+pV φ p xs)]
         [('not    (list (-t.@ p xs))) (φ+¬pV φ p xs)]
         [(_ _)
          (define Γ* (hash-update Γ Vs (λ ([ps : (℘ -h)]) (set-add ps h)) mk-∅))
          (-φ Γ* δσ)])]
      [else φ]))

  (: φ+¬pV : -φ -h (Listof -V) → -φ)
  (define (φ+¬pV φ h Vs)
    (match-define (-φ Γ δσ) φ)
    (cond
      [(andmap -t? Vs)
       (match* (h Vs)
         [('values (list (-t.@ p xs))) (φ+¬pV φ p xs)]
         [('not    (list (-t.@ p xs))) ( φ+pV φ p xs)]
         [((-</c r) Vs) (φ+pV φ (-≥/c r) Vs)]
         [((-≤/c r) Vs) (φ+pV φ (->/c r) Vs)]
         [((->/c r) Vs) (φ+pV φ (-≤/c r) Vs)]
         [((-≥/c r) Vs) (φ+pV φ (-</c r) Vs)]
         [((-not/c p) Vs) (φ+pV φ p Vs)]
         [((or (? -o?) (? -b?)) Vs) (φ+pV φ (-not/c h) Vs)])]
      [else φ]))

  (: should-call-smt? : -Γ -h (Listof -V) → Boolean)
  ;; Heuristic avoiding calling out to solvers
  ;; However this heuristic is implemented should be safe in terms of soundness.
  ;; Not calling out to solver when should only hurts precision.
  ;; Calling out to solver when there's no need only hurts performance.
  ;; TODO: re-inspect this after recent rewrite
  (define should-call-smt?
    (let ([difficult-hs {seteq '< '> '<= '>= '= 'equal? 'eq? 'eqv?}])
      (λ (Γ h Vs)
        (and
         (∋ difficult-hs h)
         (for/or : Boolean ([hs (in-hash-values Γ)]) ; TODO TR can't for*/or
           (for/or : Boolean ([h (in-set hs)])
             (∋ difficult-hs h)))))))
  )

(define-compound-unit/infer proof-system@
  (import sat-result^ static-info^ prims^ for-gc^ path^ sto^ val^ pretty-print^ env^ summ^)
  (export proof-system^ widening^ local-prover^)
  (link local-prover@ external-prover@ widening@ pre-proof-system@))
