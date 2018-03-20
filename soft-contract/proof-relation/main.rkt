#lang typed/racket/base

(provide prover@)

(require racket/match
         racket/set
         racket/bool
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
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
                  ([R (in-set R^)]
                   [Φ^* (in-value (R-_1 R))]
                   [W (in-set (R-_0 R))])
         (define-values (Φ^₁ Φ^₂) (plausible-splits Σ Φ^* 'values W fast?))
         (values (∪ truish Φ^₁) (∪ falsish Φ^₂)))]
      [(Σ Φ^ P W) (plausible-splits Σ Φ^ P W #f)]
      [(Σ Φ^ P W fast?)
       (define-values (Φ^-✓ Φ^-✗ Φ^-?) (partition-sats Σ Φ^ P W #:fast? fast?))
       (values (∪ Φ^-✓ (Φ^+ Φ^-? P W))
               (∪ Φ^-✗ (Φ^- Φ^-? P W)))]))

  (:* Φ^+ Φ^- : Φ^ V W → Φ^)
  (define (Φ^+ Φ^ P W) ???)
  (define (Φ^- Φ^ P W) ???)

  (: with-checker : (Σ Φ V (Listof V) → Valid) Σ Φ^ V W → (Values Φ^ Φ^ Φ^))
  (define (with-checker check Σ Φ^₀ P W)
    (for/fold ([Φ^-✓ : Φ^ ∅] [Φ^-✗ : Φ^ ∅] [Φ^-? : Φ^ ∅])
              ([Φ (in-set Φ^₀)])
      (case (⊔* (λ ([Vs : (Listof V)]) (check Σ Φ P Vs)) (cartesian W))
        [(✓) (values (set-add Φ^-✓ Φ) Φ^-✗ Φ^-?)]
        [(✗) (values Φ^-✓ (set-add Φ^-✗ Φ) Φ^-?)]
        [(?) (values Φ^-✓ Φ^-✗ (set-add Φ^-? Φ))])))
  )

(define-compound-unit/infer prover@
  (import evl^)
  (export prover^)
  (link sat-result@ local-prover-core@ ext-prover-core@ prover-core@))

#|
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
    (match* (h Vs)
      [('values (list (-t.@ p xs))) (apply p∋V σ φ p xs)]
      [('not    (list (-t.@ p xs))) (not-R (apply p∋V σ φ p xs))]
      [(_ _)
       (match (apply local:p∋V σ φ h Vs)
         ['? (if (should-call-smt? (-φ-condition φ) h Vs)
                 (ext:p∋V (-φ-condition φ) h Vs)
                 '?)]
         [R R])]))

  (define p∋V^ (local:lift-p∋V p∋V))
  (define quick-p∋V^ local:p∋V^)
  
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
          (-φ (Γ+pV Γ h Vs) δσ)])]
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

  (: Γ+pV : -Γ -h (Listof -t) → -Γ)
  (define (Γ+pV Γ p Vs)
    (: upd : -Γ -h -t → -Γ)
    (define (upd Γ h t)
      (cond [(-b? t) Γ]
            [else (hash-update Γ t (λ ([ps : (℘ -h)]) (set-add ps h)) mk-∅)]))
    (match* (p Vs)
      [('>  (list t₁ t₂)) (upd (upd Γ (->/c t₂) t₁) (-</c t₁) t₂)]
      [('>= (list t₁ t₂)) (upd (upd Γ (-≥/c t₂) t₁) (-≤/c t₁) t₂)]
      [('<  (list t₁ t₂)) (upd (upd Γ (-</c t₂) t₁) (->/c t₁) t₂)]
      [('<= (list t₁ t₂)) (upd (upd Γ (-≤/c t₂) t₁) (-≥/c t₁) t₂)]
      [((or '= 'equal? 'eq? 'eqv? 'string=? 'char=?) (list t₁ t₂))
       (upd (upd Γ (-≡/c t₂) t₁) (-≡/c t₁) t₂)]
      [((-not/c (or '= 'equal? 'eq? 'eqv? 'string=? 'char=?)) (list t₁ t₂))
       (upd (upd Γ (-not/c (-≡/c t₂)) t₁) (-not/c (-≡/c t₁)) t₂)]
      [('arity-includes? (list t (-b (? Arity? a)))) (upd Γ (-arity-includes/c a) t)]
      [(p (list t)) (upd Γ p t)]
      [(_ _) Γ]))

  (: should-call-smt? : -Γ -h (Listof -V) → Boolean)
  ;; Heuristic avoiding calling out to solvers
  ;; However this heuristic is implemented should be safe in terms of soundness.
  ;; Not calling out to solver when should only hurts precision.
  ;; Calling out to solver when there's no need only hurts performance.
  ;; TODO: re-inspect this after recent rewrite
  (define should-call-smt?
    (let ([difficult?
           (match-λ?
            '< '> '<= '>= '= 'zero?
            (? -</c?) (? ->/c?) (? -≤/c?) (? -≥/c?))])
      (λ (Γ h Vs)
        (and
         (difficult? h)
         (for/or : Boolean ([hs (in-hash-values Γ)]) ; TODO TR can't for*/or
           (for/or : Boolean ([h (in-set hs)])
             (difficult? h)))))))
  )


|#
