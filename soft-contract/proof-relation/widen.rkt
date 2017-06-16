#lang typed/racket/base

(provide widening@)

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/set
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit widening@
  (import local-prover^ pc^ sto^ pretty-print^ env^ val^)
  (export widening^)

  ;; Strengthen path condition `Γ` with `s`
  (define (Γ+ [Γ : -Γ] . [ts : -?t *]) : -Γ
    (match-define (-Γ φs as) Γ)
    (define φs*
      (for/fold ([φs : (℘ -t) φs]) ([t ts]
                                    #:when t
                                    #:unless (set-empty? (fvₜ t)))
        (define t*
          (match t
            [(-t.@ 'not (list (-t.@ 'not (list t*)))) t*]
            [_ t]))
        (φs+ φs t*)))
    (-Γ φs* as))

  (define (Γ++ [Γ : -Γ] [φs : (℘ -t)]) : -Γ (apply Γ+ Γ (set->list φs)))

  (define (σ⊕! [Σ : -Σ] [Γ : -Γ] [⟪α⟫ : ⟪α⟫] [W : -W¹] #:mutating? [mutating? : Boolean #f]) : Void
    (match-define (-W¹ V s) W)
    (σ⊕V! Σ ⟪α⟫ (V+ (-Σ-σ Σ) V (predicates-of Γ s)) #:mutating? mutating?))

  (define (σ⊕V! [Σ : -Σ] [α : ⟪α⟫] [V : -V] #:mutating? [mutating? : Boolean #f]) : Void
    (match-define (-Σ σ _ _) Σ)
    (set--Σ-σ! Σ (σ⊕ σ α V mutating?)))

  (: σ⊕Vs! : -Σ ⟪α⟫ (℘ -V) → Void)
  (define (σ⊕Vs! Σ α Vs)
    (match-define (-Σ (and σ (-σ σm ms cs)) _ _) Σ)
    (define σm*
      (hash-update σm
                   α
                   (λ ([Vs₀ : (℘ -V)])
                     (cond [(set-empty? Vs₀) Vs] ; fast special case
                           [else
                            (for/fold ([Vs* : (℘ -V) Vs₀])
                                      ([V (in-set Vs)])
                              (Vs⊕ σ Vs* V))]))
                   mk-∅))
    (set--Σ-σ! Σ (-σ σm* ms cs)))

  (: σ-copy! : -Σ ⟪α⟫ ⟪α⟫ → Void)
  (define (σ-copy! Σ α-src α-tgt)
    (unless (equal? α-src α-tgt)
      (σ⊕Vs! Σ α-tgt (σ@ Σ α-src))))

  (define (σ⊕ [σ : -σ] [α : ⟪α⟫] [V : -V] [α.mutating? : Boolean]) : -σ
    (match-define (-σ store mutated cardinalities) σ)
    
    (define do-strong-update?
      (let ([α.ambiguous? (equal? 'N (hash-ref cardinalities α (λ () 0)))]
            [α.mutated? (∋ mutated α)])
        (and α.mutating? (not α.mutated?) (not α.ambiguous?))))
    
    (define store*
      (if do-strong-update?
          (hash-set store α {set V})
          (hash-update store α (λ ([Vs : (℘ -V)]) (Vs⊕ σ Vs V)) mk-∅)))
    
    (define mutated* (if α.mutating? (set-add mutated α) mutated))

    (define cardinalities*
      (cond
        [do-strong-update? cardinalities]
        [;; Cheat for top-level reference.
         ;; A top-level binding may be (spuriously) bound twice due to
         ;; prior path-condition splits
         (-𝒾? (⟪α⟫->-α α))
         (hash-update cardinalities α
                      (match-lambda
                        ['0 1]
                        ['1 1]
                        ['N 'N])
                      (λ () 0))]
        [else (hash-update cardinalities α cardinality+ (λ () 0))]))
    
    (-σ store* mutated* cardinalities*))

  ;; Widen value set with new value
  (define (Vs⊕ [σ : -σ] [Vs : (℘ -V)] [V : (U -V (℘ -V))]) : (℘ -V)
    (: iter : (℘ -V) -V → (U (℘ -V) (Pairof (℘ -V) -V)))
    (define (iter Vs V)
      (match (for/or : (Option (List -V -V -V)) ([Vᵢ Vs])
               (cond [(V⊕ σ Vᵢ V) => (λ ([V* : -V]) (list V* Vᵢ V))]
                     [else #f]))
        [(list V* V₁ V₂)
         (cons (set-remove (set-remove Vs V₁) V₂)
               V*)]
        [#f (set-add Vs V)]))

    (: repeat-compact (∀ (X) (℘ X) X ((℘ X) X → (U (℘ X) (Pairof (℘ X) X))) → (℘ X)))
    (define (repeat-compact xs x f)
      (let loop ([xs : (℘ X) xs] [x : X x])
        (match (f xs x)
          [(cons xs* x*) (loop xs* x*)]
          [(? set? s) s])))

    (cond [(-V? V) (repeat-compact Vs V iter)]
          [else (for/fold ([Vs* : (℘ -V) Vs])
                          ([Vᵢ (in-set V)])
                  (repeat-compact Vs Vᵢ iter))]))

  ;; Refine opaque value with predicate
  (define (V+ [σ : -σ] [V : -V] [P : (U -V -h (℘ -h))]) : -V
    
    (define (simplify [P : -V]) : -V
      (match P
        [(-Ar _ (and α (app ⟪α⟫->-α (or (? -α.wrp?) (? -e?)))) _)
         (define Vs (σ@ σ α))
         (cond [(= 1 (set-count Vs)) (simplify (set-first Vs))]
               [else P])]
        [(-St/C _ 𝒾 _) (-st-p 𝒾)]
        [(or (? -Vectorof?) (? -Vector/C?)) 'vector?]
        [_ P]))
    
    (with-debugging/off ((V*) (cond
                                [(set? P)
                                 (for/fold ([V : -V V]) ([Pᵢ (in-set P)])
                                   (V+ σ V Pᵢ))]
                                [else
                                 (with-debugging/off
                                   ((V*)
                                    (match V
                                      [(-● ps)
                                       (match P
                                         [(-≡/c b) (-b b)]
                                         ['not -ff]
                                         ['null? -null]
                                         ['void? -void]
                                         [(? -h? h) (-● (ps+ ps h))]
                                         [(? -V? P)
                                          (match (simplify P)
                                            [(? -o? o) (-● (ps+ ps o))]
                                            [_ V])])]
                                      [_ V]))
                                   
                                   (hash-ref! printing (list V P)
                                              (λ ()
                                                (printf "~a + ~a -> ~a~n"
                                                        (show-V V)
                                                        (if (-v? P) (show-e P) (show-V P))
                                                        (show-V V*)))))]))

      (when (-●? V)
        (: show-P : (U -v -V (℘ -v) (℘ -V)) → Sexp)
        (define (show-P P)
          (cond [(set? P) (set-map P show-P)]
                [(-V? P) (show-V P)]
                [else (show-e P)]))
        
        (printf "V+ ~a ~a -> ~a~n~n" (show-V V) (show-P P) (show-V V*)))))

  ;; Combine 2 predicates for a more precise one.
  ;; Return `#f` if there's no single predicate that refines both
  (define p+ : (-h -h → (Option (℘ -h)))
    (match-lambda**/symmetry
     [(p q) #:when (equal? '✓ (p⇒p p q)) {set p}]
     [((or 'exact-integer? 'exact-nonnegative-integer?)
       (-≥/c (and (? (between/c 0 1)) (not 0))))
      {set 'exact-positive-integer?}]
     [((or 'exact-integer? 'exact-nonnegative-integer?)
       (->/c (and (? (between/c 0 1)) (not 1))))
      {set 'exact-positive-integer?}]
     [('exact-integer? (-≥/c (and (? (between/c -1 0)) (not -1))))
      {set 'exact-nonnegative-integer?}]
     [('exact-integer? (->/c (and (? (between/c -1 0)) (not  0))))
      {set 'exact-nonnegative-integer?}]
     [('exact-nonnegative-integer? (-not/c (-≡/c 0)))
      {set 'exact-positive-integer?}]
     [('exact-nonnegative-integer? (-≢/c 0))
      {set 'exact-positive-integer?}]
     [('list? (-not/c 'null?)) {set 'list? -cons?}]
     [('list? (-not/c -cons?)) {set 'null?}]
     [(_ _) #f]))

  ;; Strengthen refinement set with new predicate
  (define (ps+ [ps : (℘ -h)] [p : -h]) : (℘ -h)

    (: iter : (℘ -h) -h → (U (℘ -h) (Pairof (℘ -h) (℘ -h))))
    (define (iter ps p)
      (match (for/or : (Option (List (℘ -h) -h -h)) ([pᵢ ps])
               (cond [(p+ pᵢ p) => (λ ([ps* : (℘ -h)]) (list ps* pᵢ p))]
                     [else #f]))
        [(list ps* pᵢ p)
         (cons (set-remove (set-remove ps pᵢ) p)
               ps*)]
        [#f (set-add ps p)]))

    (: repeat-compact (∀ (X) (℘ X) X ((℘ X) X → (U (℘ X) (Pairof (℘ X) (℘ X)))) → (℘ X)))
    (define (repeat-compact xs x f)
      (let loop ([xs : (℘ X) xs] [x : X x])
        (match (f xs x)
          [(cons xs₁ xs₂)
           (for/fold ([acc : (℘ X) xs₁]) ([x xs₂])
             (loop acc x))]
          [(? set? s) s])))

    (case p
      [(any/c) ps] ; TODO tmp hack. How did this happen?
      [else (repeat-compact ps p iter)]))

  (define (φs+ [φs : (℘ -t)] [φ : -t]) : (℘ -t)
    
    (: iter : (℘ -t) -t → (U (℘ -t) (Pairof (℘ -t) (℘ -t))))
    (define (iter φs φ)
      (match (for/or : (Option (List (℘ -t) -t -t)) ([φᵢ φs])
               (cond [(φ+ φᵢ φ) => (λ ([φs* : (℘ -t)]) (list φs* φᵢ φ))]
                     [else #f]))
        [(list φs* φᵢ φ)
         (cons (set-remove (set-remove φs φᵢ) φ)
               φs*)]
        [#f (set-add φs φ)]))

    (: repeat-compact (∀ (X) (℘ X) X ((℘ X) X → (U (℘ X) (Pairof (℘ X) (℘ X)))) → (℘ X)))
    ;; FIXME code duplicate
    (define (repeat-compact xs x f)
      (let loop ([xs : (℘ X) xs] [x : X x])
        (match (f xs x)
          [(cons xs₁ xs₂)
           (for/fold ([acc : (℘ X) xs₁]) ([x xs₂])
             (loop acc x))]
          [(? set? s) s])))

    (repeat-compact φs φ iter))

  (define φ+ : (-t -t → (Option (℘ -t)))
    (match-lambda**/symmetry ; FIXME inefficiency, there's no e⊢e
     [(φ ψ) #:when (equal? '✓ (Γ⊢t {set φ} ψ)) {set φ}]
     [(_ _) #f]))

  ;; Widen 2 values to one approximating both.
  ;; Return `#f` if no approximation preferred
  (define (V⊕ [σ : -σ] [V₁ : -V] [V₂ : -V]) : (Option -V)
    (with-debugging ((V*) (match* (V₁ V₂)
                            [(_ _) #:when (V⊑ σ V₂ V₁) V₁]
                            [(_ _) #:when (V⊑ σ V₁ V₂) V₂]
                            ; TODO more heuristics
                            [((-b b₁) (-b b₂)) #:when (not (equal? b₁ b₂))
                             (define-syntax-rule (check-for-base-types p? ...)
                               (cond
                                 [(and (p? b₁) (p? b₂)) (-● {set 'p?})] ...
                                 [else #f]))

                             (check-for-base-types
                              exact-positive-integer? exact-nonnegative-integer? exact-integer?
                              integer? real? number?
                              path-string? string?
                              char? boolean?
                              regexp? pregexp? byte-regexp? byte-pregexp?)]
                            [((? -b? b) (-● ps))
                             (define ps*
                               (for/set: : (℘ -h) ([p (in-set ps)]
                                                   #:when (equal? '✓ (p∋Vs σ p b)))
                                 p))
                             ;; guard non-empty set means heuristic, that they're "compatible"
                             (and (not (set-empty? ps*)) (-● ps*))]
                            [((-● ps) (-● qs))
                             (define ps* (ps⊕ ps qs))
                             (if (set-empty? ps*) #|just a heuristic|# #f (-● ps*))]
                            [(_ _) #f]))
      (when (or (let ([●? (λ (V) (and (-V? V) (equal? V (-● ∅))))])
                  (and (●? V*) (not (●? V₁)) (not (●? V₂)))))
        (printf "Warning: ~a ⊕ ~a = ~a~n~n" (show-V V₁) (show-V V₂) (show-V V*)))))

  ;; Return refinement set that's an over-approximation of both sets
  (define (ps⊕ [ps₁ : (℘ -h)] [ps₂ : (℘ -h)]) : (℘ -h)
    (for*/union : (℘ -h) ([p₁ ps₁] [p₂ ps₂]) (p⊕ p₁ p₂)))

  ;; Return predicate that's weaker than both
  (define p⊕ : (-h -h → (℘ -h))
    (match-lambda**/symmetry
     [(p q) #:when (equal? '✓ (p⇒p q p)) {set p}]
     [(_ _) ∅]))

  ;; Check if `V₂` definitely subsumes `V₁`
  ;; `#f` is a conservative "don't know" answer
  (define (V⊑ [σ : -σ] [V₁ : -V] [V₂ : -V]) : Boolean

    (define-set seen : (Pairof ⟪α⟫ ⟪α⟫) #:as-mutable-hash? #t)

    (: go/⟪α⟫ : ⟪α⟫ ⟪α⟫ → Boolean)
    (define (go/⟪α⟫ α₁ α₂)
      (cond
        [(equal? α₁ α₂) #t]
        [else
         (define α₁α₂ (cons α₁ α₂))
         (cond
           [(seen-has? α₁α₂) #t]
           [else
            (seen-add! α₁α₂)
            (define Vs₁ (σ@ σ α₁))
            (define Vs₂ (σ@ σ α₂))
            (for/and : Boolean ([V₁ (in-set Vs₁)])
              (for/or : Boolean ([V₂ (in-set Vs₂)])
                (go V₁ V₂)))])]))

    (: go : -V -V → Boolean)
    (define (go V₁ V₂)
      (match* (V₁ V₂)
        [(V V) #t]
        [(_ (-● ps)) #:when (not (behavioral? σ V₁))
         (for/and : Boolean ([p ps])
           (equal? '✓ (p∋Vs σ p V₁)))]
        [((-St 𝒾 αs₁) (-St 𝒾 αs₂)) #:when (struct-all-immutable? 𝒾)
         (for/and : Boolean ([α₁ : ⟪α⟫ αs₁] [α₂ : ⟪α⟫ αs₂])
           (go/⟪α⟫ α₁ α₂))]
        [((-Clo _ ⟦e⟧ ρ₁ _)
          (-Clo _ ⟦e⟧ ρ₂ _)) ; TODO : ignore `Γ` ok?
         (for/and : Boolean ([(x α₁) (in-hash ρ₁)])
           (go/⟪α⟫ α₁ (ρ@ ρ₂ x)))]
        [(_ _) #f]))

    (go V₁ V₂))

  (define (φs⊑ [φs₁ : (℘ -t)] [φs₂ : (℘ -t)]) : Boolean (⊆ φs₂ φs₁))

  (define (Γ⊑ [Γ₁ : -Γ] [Γ₂ : -Γ]) : Boolean
    (match-define (-Γ φs₁ as₁) Γ₁)
    (match-define (-Γ φs₂ as₂) Γ₂)
    (and (equal? as₁ as₂) (⊆ φs₂ φs₁)))

  (define (?Γ⊔ [Γ₁ : (℘ -t)] [Γ₂ : (℘ -t)]) : (Option (℘ -t))
    (define-values (Γ* δΓ₁ δΓ₂) (set-intersect/differences Γ₁ Γ₂))
    (cond [(and (= 1 (set-count δΓ₁))
                (= 1 (set-count δΓ₂)))
           (define φ₁ (set-first δΓ₁))
           (define φ₂ (set-first δΓ₂))
           (cond [(complement? φ₁ φ₂) Γ*]
                 [(Γ⊢t {set φ₁} φ₂) Γ₂]
                 [(Γ⊢t {set φ₂} φ₁) Γ₁]
                 [else #f])]
          [else #f]))

  (define ((?ΓA⊔ [σ : -σ]) [ΓA₁ : -ΓA] [ΓA₂ : -ΓA]) : (Option -ΓA)

    (: A⊑ : -σ -A -A → Boolean)
    (define (A⊑ σ A₁ A₂)
      (match* (A₁ A₂)
        [((-W Vs₁ s₁) (-W Vs₂ s₂))
         (and (equal? s₁ s₂)
              (= (length Vs₁) (length Vs₂))
              (for/and : Boolean ([V₁ Vs₁] [V₂ Vs₂])
                (V⊑ σ V₁ V₂)))]
        [((? -blm? blm₁) (? -blm? blm₂))
         (equal? blm₁ blm₂)]
        [(_ _) #f]))

    (: ΓA⊑ : -ΓA -ΓA → Boolean)
    (define (ΓA⊑ ΓA₁ ΓA₂)
      (match-define (-ΓA Γ₁ A₁) ΓA₁)
      (match-define (-ΓA Γ₂ A₂) ΓA₂)
      (and (φs⊑ Γ₁ Γ₂) (A⊑ σ A₁ A₂)))
    
    (cond [(ΓA⊑ ΓA₁ ΓA₂) ΓA₂]
          [(ΓA⊑ ΓA₂ ΓA₁) ΓA₁]
          [else
           (match-define (-ΓA Γ₁ A₁) ΓA₁)
           (match-define (-ΓA Γ₂ A₂) ΓA₂)
           (define ?Γ (and (equal? A₁ A₂) (?Γ⊔ Γ₁ Γ₂)))
           (and ?Γ (-ΓA ?Γ A₂))]))

  (define (M⊕ [M : -M] [σ : -σ] [αₖ : -αₖ] [Γ : (℘ -t)] [A : -A]) : -M
    (hash-update M αₖ (set-add/compact (-ΓA Γ A) (?ΓA⊔ σ)) mk-∅))

  (define (M⊕! [Σ : -Σ] [αₖ : -αₖ] [Γ : (℘ -t)] [A : -A]) : Void
    (match-define (-Σ σ _ M) Σ)
    (set--Σ-M! Σ (M⊕ M σ αₖ Γ A)))

  (define (σₖ⊕! [Σ : -Σ] [αₖ : -αₖ] [κ : -κ]) : Void
    (match-define (-Σ _ σₖ _) Σ)
    (set--Σ-σₖ! Σ (σₖ⊕ σₖ αₖ κ)))

  (define (?κ⊔ [κ₁ : -κ] [κ₂ : -κ]) : (Option -κ)

    (: t⊑ : -?t -?t → Boolean)
    (define t⊑
      (match-lambda**
       [(_ #f) #t]
       [(t t ) #t]
       [(_ _ ) #f]))

    (: κ⊑ : -κ -κ → Boolean)
    (define (κ⊑ κ₁ κ₂)
      (match-define (-κ ⟦k⟧₁ Γ₁ ⟪ℋ⟫₁ args₁) κ₁)
      (match-define (-κ ⟦k⟧₂ Γ₂ ⟪ℋ⟫₂ args₂) κ₂)
      (and (equal? ⟦k⟧₁ ⟦k⟧₂)
           (equal? ⟪ℋ⟫₁ ⟪ℋ⟫₂)
           (andmap t⊑ args₁ args₂)
           (Γ⊑ Γ₁ Γ₂)))

    (cond [(κ⊑ κ₁ κ₂) κ₂]
          [(κ⊑ κ₂ κ₁) κ₁]
          [else
           (match-define (-κ ⟦k⟧₁ (-Γ φs₁ as₁) ⟪ℋ⟫₁ args₁) κ₁)
           (match-define (-κ ⟦k⟧₂ (-Γ φs₂ as₂) ⟪ℋ⟫₂ args₂) κ₂)
           (cond [(and (equal? ⟦k⟧₁ ⟦k⟧₂)
                       (equal? ⟪ℋ⟫₁ ⟪ℋ⟫₂)
                       (andmap t⊑ args₁ args₂)
                       (equal? as₁ as₂))
                  (define ?φs (?Γ⊔ φs₁ φs₂))
                  (and ?φs (-κ ⟦k⟧₂ (-Γ ?φs as₂) ⟪ℋ⟫₂ args₂))]
                 [else #f])]))

  (define (σₖ⊕ [σₖ : -σₖ] [αₖ : -αₖ] [κ : -κ]) : -σₖ
    (hash-update σₖ αₖ (set-add/compact κ ?κ⊔) mk-∅))

  ;; Extract predicates of `W`'s symbol that are not already implied by `W`'s value
  (define (predicates-of-W [σ : -σ] [Γ : -Γ] [W : -W¹]) : (U (℘ -h) -⟦e⟧)
    (match-define (-W¹ V t) W)
    (define ps₁ : (U (℘ -h) -⟦e⟧)
      (match V
        [(-● ps) ps]
        [(-St 𝒾 _) {set (-st-p 𝒾)}]
        [(-St* (-St/C _ 𝒾 _) _ _) {set (-st-p 𝒾)}]
        [(-Clo _ ⟦e⟧ _ _) ⟦e⟧]
        [(-b (list)) {set 'null?}]
        [_ ∅]))
    (cond
      [(set? ps₁)
       (define ps₂
         (for/set: : (℘ -h) ([p (predicates-of Γ t)]
                             #:unless (and #|HACK|# (-●? V) (equal? '✓ (p∋Vs σ p V))))
           p))
       (∪ ps₁ ps₂)]
      [else
       ps₁]))

  (define (add-leak! [Σ : -Σ] [V : -V]) : Void
    (when (behavioral? (-Σ-σ Σ) V)
      (σ⊕V! Σ ⟪α⟫ₕᵥ V)))

  ;; Convert invariants about arguments in caller into those about parameters in callee
  (define (inv-caller->callee [σ : -σ]
                              [fvs : (℘ Symbol)]
                              [fml : -formals]
                              [Ws : (Listof -W¹)]
                              [Γₑᵣ : -Γ]
                              [Γₑₑ : -Γ]) : -Γ

    (match-define (-Γ φsₑₑ asₑₑ) Γₑₑ)
    (define asₑₑ* (accum-aliases asₑₑ fml (map -W¹-t Ws)))

    (define xs : (Listof Symbol)
      (match fml
        [(? list? xs) xs]
        [(-var xs _ ) xs]))

    (define-values (arg->x x->V)
      (for/fold ([arg->x : (HashTable -t Symbol) (hash)]
                 [x->V : (HashTable Symbol -V) (hasheq)])
                ([x xs] [W Ws]
                 #:when (-W¹-t W)
                 #:unless (hash-has-key? arg->x (-W¹-t W)))
        (values (hash-set arg->x (-W¹-t W) x)
                (hash-set x->V x (-W¹-V W)))))

    (: er->ee : -t → -?t)
    (define (er->ee t)

      (: keep? : -t → Boolean)
      (define keep?
        (set->predicate
         (for/union : (℘ -t) ([x fvs])
                    (cond [(hash-ref asₑₑ x #f) =>
                           (λ ([t* : -t]) {set t t*})]
                          [else {set t}]))))

      (match t
        [arg #:when (hash-has-key? arg->x arg)
             (define xₜ (hash-ref arg->x arg))
             (hash-ref asₑₑ* xₜ (λ () (-x xₜ)))]
        [(-t.@ f xs)
         (and (h-unique? f)
              (let ([xs* (map er->ee xs)])
                (and (andmap -t? xs*) (-t.@ f xs*))))]
        [(? -prim? b) b]
        [(? -𝒾? 𝒾) 𝒾]
        [t (and (keep? t) t)]))

    ;; Avoid redundant symbols that may blow up the state unnecessarily
    (define (redundant? [t : -t])
      (match t
        [(-t.@ (? -o? o) (list (-x x)))
         (cond [(hash-ref x->V x #f) =>
                (λ ([V : -V])
                  (equal? '✓ (p∋Vs σ o V)))]
               [else #f])]
        [_ #f]))

    (define φsₑₑ*
      (for*/fold ([φsₑₑ* : (℘ -t) φsₑₑ])
                 ([t (in-set (-Γ-facts Γₑᵣ))]
                  [t* (in-value (er->ee t))]
                  #:when t*
                  #:unless (redundant? t*))
        (set-add φsₑₑ* t*)))

    (with-debugging/off ((Γₑₑ*) (-Γ φsₑₑ* asₑₑ*))
      (printf "caller->callee: ~a -> ~a~n" (show-formals fml) (map show-W¹ Ws))
      (printf "free: ~a~n" (set->list fvs))
      (printf "  - Γₑᵣ : ~a~n"   (show-Γ Γₑᵣ))
      (printf "  - Γₑₑ : ~a~n"   (show-Γ Γₑₑ))
      (printf "  - Γₑₑ*: ~a~n~n" (show-Γ Γₑₑ*))))

  (define (accum-aliases [as : (HashTable Symbol -t)]
                         [fml : -formals]
                         [args : (Listof -?t)]) : (HashTable Symbol -t)

    (define xs : (Listof Symbol)
      (match fml
        [(? list? xs) xs]
        [(-var xs _ ) xs]))

    ;; specific inlining hack just for `octy/ex-{08,12}.rkt`, `mochi/intro3.rkt`
    ;; To get rid of this hack and generalize for precision, need to make it aware of loops
    (define (restrictedly-occured? [t : -t])
      (with-debugging/off ((res?) (for/or : Boolean ([(x₀ t₀) (in-hash as)])
                                    (match? t (-t.@ (? h-unique?) (or (list (== t₀))
                                                                      (list (== t₀) (? -b?))))
                                            (== t₀))))
        (printf "restrictedly-occured? ~a: ~a~n" (show-t t) res?)))

    (define-values (as* _)
      (for/fold ([as* : (HashTable Symbol -t) as]
                 [seen : (HashTable -t -t) (hash)])
                ([x xs] [arg args])
        (cond
          [arg
           (cond
             [(hash-ref seen arg #f) =>
              (λ ([t₀ : -t])
                (values (hash-set as* x t₀) seen))]
             [(restrictedly-occured? arg)
              (values (hash-set as* x arg)
                      (hash-set seen arg arg))]
             [else (values as (hash-set seen arg (-x x)))])]
          [else (values as seen)])))

    #;(begin
        (printf "accum-aliases: ~a ↦ ~a~n" (show-formals fml) (map show-t args))
        (printf "  - old: ~a~n" as)
        (printf "  - new: ~a~n" as*)
        (printf "~n"))
    as*)

  ;; Propagate simple predicate back to caller
  (define (inv-callee->caller [σ : -σ]
                              [fvs : (℘ Symbol)]
                              [fml : -formals]
                              [ts : (Listof -?t)]
                              [Γₑᵣ : -Γ]
                              [Γₑₑ : -Γ]) : (Option -Γ)
    (match-define (-Γ φsₑₑ asₑₑ) Γₑₑ)
    (match-define (-Γ φsₑᵣ asₑᵣ) Γₑᵣ)

    (define param->arg
      (let ([xs
             (match fml
               [(-var xs _) xs]
               [(? list? xs) xs])])
        (for/hash : (HashTable -t -t) ([x xs] [tₓ ts] #:when tₓ)
          (values (hash-ref asₑₑ x (λ () (-x x))) tₓ))))

    (: ee->er : -t → -?t)
    (define (ee->er φ)
      (match φ
        [x #:when (hash-has-key? param->arg x) (hash-ref param->arg x)]
        [(-t.@ p (list x))
         #:when (and (h-syntactic? p) (hash-has-key? param->arg x))
         (-t.@ p (list (hash-ref param->arg x)))]
        [(-t.@ 'not (list ψ))
         (define ψ* (ee->er ψ))
         (and ψ* (-t.@ 'not (list ψ*)))]
        [(-t.@ (? -special-bin-o? o) (list x (? -b? b)))
         #:when (hash-has-key? param->arg x)
         (-t.@ o (list (hash-ref param->arg x) b))]
        [(-t.@ (? -special-bin-o? o) (list (? -b? b) x))
         #:when (hash-has-key? param->arg x)
         (-t.@ o (list b (hash-ref param->arg x)))]
        [_ #f]))

    (define φsₑᵣ*
      (for*/fold ([acc : (Option (℘ -t)) φsₑᵣ])
                 ([φ (in-set φsₑₑ)] #:break (not acc)
                  [φ* (in-value (ee->er φ))] #:when φ*)
        (and (not (equal? φ* -ff)) (set-add (assert acc) φ*))))

    #;(begin
        (printf "inv-callee->caller: ~a ↦ ~a~n" fml (map show-t ts))
        (printf "  - ee : ~a~n" (set-map φsₑₑ  show-t))
        (printf "  - er : ~a~n" (set-map φsₑᵣ  show-t))
        (printf "  - er*: ~a~n" (and φsₑᵣ* (set-map φsₑᵣ* show-t)))
        (printf "~n"))

    (and φsₑᵣ* (-Γ φsₑᵣ* asₑᵣ)))

  (: alloc-init-args! : -Σ -Γ -ρ -⟪ℋ⟫ -?t (Listof Symbol) (Listof -W¹) → -ρ)
  (define (alloc-init-args! Σ Γₑᵣ ρₑₑ ⟪ℋ⟫ sₕ xs Ws)
    
    (define φsₕ
      (let* ([bnd (list->seteq xs)]
             [fvs (set-subtract (if (or (-λ? sₕ) (-case-λ? sₕ)) (fvₜ sₕ) ∅eq) bnd)])
        (for*/set: : (℘ -t) ([φ (in-set (-Γ-facts Γₑᵣ))]
                             [fv⟦φ⟧ (in-value (fvₜ φ))]
                             #:unless (set-empty? fv⟦φ⟧)
                             #:when (⊆ fv⟦φ⟧ fvs))
          φ)))
    (define ρ₀ (ρ+ ρₑₑ -x-dummy (-α->⟪α⟫ (-α.fv ⟪ℋ⟫ φsₕ))))
    (for/fold ([ρ : -ρ ρ₀]) ([x xs] [Wₓ Ws])
      (match-define (-W¹ Vₓ sₓ) Wₓ)
      (define α (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ ∅ #;(predicates-of-W (-Σ-σ Σ) Γₑᵣ Wₓ))))
      (σ⊕! Σ Γₑᵣ α Wₓ)
      (ρ+ ρ x α)))

  (: alloc-rest-args! ([-Σ -Γ -⟪ℋ⟫ -ℒ (Listof -W¹)] [#:end -V] . ->* . -V))
  (define (alloc-rest-args! Σ Γ ⟪ℋ⟫ ℒ Ws #:end [Vₙ -null])

    (: precise-alloc! ([(Listof -W¹)] [Natural] . ->* . -V))
    ;; Allocate vararg list precisely, preserving length
    (define (precise-alloc! Ws [i 0])
      (match Ws
        [(list) Vₙ]
        [(cons Wₕ Ws*)
         (define αₕ (-α->⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ i)))
         (define αₜ (-α->⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ i)))
         (σ⊕! Σ Γ αₕ Wₕ)
         (σ⊕V! Σ αₜ (precise-alloc! Ws* (+ 1 i)))
         (-Cons αₕ αₜ)]))
    
    ;; Allocate length up to 2 precisely to let `splay` to go through
    ;; This is because `match-lambda*` expands to varargs with specific
    ;; expectation of arities
    (match Ws
      [(or (list) (list _) (list _ _) (list _ _ _))
       (precise-alloc! Ws)]
      [(? pair?)
       (define αₕ (-α->⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ #f)))
       (define αₜ (-α->⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ #f)))
       (define Vₜ (-Cons αₕ αₜ))
       ;; Allocate spine for var-arg lists
       (σ⊕V! Σ αₜ Vₜ)
       (σ⊕V! Σ αₜ Vₙ)
       ;; Allocate elements in var-arg lists
       (for ([W Ws])
         (σ⊕! Σ Γ αₕ W))
       Vₜ]))

  (: estimate-list-lengths : -σ -V → (℘ (U #f Arity)))
  ;; Estimate possible list lengths from the object language's abstract list
  (define (estimate-list-lengths σ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define maybe-non-proper-list? : Boolean #f)

    (: arity-inc : Arity → Arity)
    (define arity-inc
      (match-lambda
        [(? exact-integer? n) (+ 1 n)]
        [(arity-at-least n) (arity-at-least (+ 1 n))]))
    
    (: go! : -V → (℘ Arity))
    (define go!
      (match-lambda
        [(-Cons _ αₜ)
         (cond [(seen-has? αₜ) {set (arity-at-least 0)}]
               [else (seen-add! αₜ)
                     (for/union : (℘ Arity) ([Vₜ (in-set (σ@ σ αₜ))])
                        (map/set arity-inc (go! Vₜ)))])]
        [(-b '()) {set 0}]
        [_ (set! maybe-non-proper-list? #t)
           ∅]))
    (define res
      (match (normalize-arity (set->list (go! V)))
        [(? list? l) (list->set l)]
        [a {set a}]))
    (if maybe-non-proper-list? (set-add res #f) res))

  (: unalloc : -σ -V → (℘ (Option (Listof -V))))
  ;; Convert a list in the object language into list(s) in the meta language
  (define (unalloc σ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define Tail {set '()})
    (: go! : -V → (℘ (Listof -V)))
    (define go!
      (match-lambda
        [(-Cons αₕ αₜ)
         (cond
           [(seen-has? αₜ) Tail]
           [else
            (seen-add! αₜ)
            (define tails
              (for/union : (℘ (Listof -V)) ([Vₜ (in-set (σ@ σ αₜ))])
                 (go! Vₜ)))
            (define heads (σ@ σ αₕ))
            (for*/set: : (℘ (Listof -V)) ([head (in-set heads)] [tail (in-set tails)])
              (cons head tail))])]
        [(-b (list)) Tail]
        [_ ∅]))

    ;; FIXME this list is complete and can result in unsound analysis
    ;; Need to come up with a nice way to represent an infinite family of lists
    (go! V))

  (: unalloc-prefix : -σ -V Natural → (℘ (Pairof (Listof -V) -V)))
  (define (unalloc-prefix σ V n)
    (let go ([V : -V V] [n : Natural n])
      (cond
        [(<= n 0) {set (cons '() V)}]
        [else
         (match V
           [(-Cons αₕ αₜ)
            (define Vₕs (σ@ σ αₕ))
            (define pairs
              (for/union : (℘ (Pairof (Listof -V) -V)) ([Vₜ (in-set (σ@ σ αₜ))])
                         (go Vₜ (- n 1))))
            (for*/set: : (℘ (Pairof (Listof -V) -V)) ([Vₕ (in-set Vₕs)]
                                                      [pair (in-set pairs)])
              (match-define (cons Vₜs Vᵣ) pair)
              (cons (cons Vₕ Vₜs) Vᵣ))]
           [_ ∅])])))
  )


(define-syntax match-lambda**/symmetry
  ;; b/c TR doesn't work well with `match-lambda*` and `list-no-order`
  (syntax-parser
    [(_ clauses ... [((~literal _) (~literal _)) dflt ...])
     (define doubled-clauses
       (append-map
        (λ (clause)
          (with-syntax ([[(x y) e ...] clause])
            (list #'[(x y) e ...] #'[(y x) e ...])))
        (syntax->list #'(clauses ...))))
     #`(match-lambda** #,@doubled-clauses [(_ _) dflt ...])]))
