#lang typed/racket/base

(provide widening@)

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/list
         racket/set
         racket/bool
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit widening@
  (import static-info^ local-prover^ pc^ sto^ pretty-print^ env^ val^ summ^)
  (export widening^)

  (: Γ+ : -Γ -?t * → -Γ)
  ;; Strengthen path condition `Γ` with `s`
  (define (Γ+ Γ . ts)

    (: φs+ : -Γ -t → -Γ)
    (define (φs+ φs φ)      
      
      (: iter : -Γ -t → (U -Γ (Pairof -Γ -Γ)))
      (define (iter φs φ)
        (match (for/or : (Option (List -Γ -t -t)) ([φᵢ φs])
                 (cond [(φ+ φᵢ φ) => (λ ([φs* : -Γ]) (list φs* φᵢ φ))]
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
    
    (for/fold ([Γ : -Γ Γ])
              ([t ts]
               #:when t
               ;#:unless (set-empty? (fvₜ t))
               )
      (define t*
        (match t
          [(-t.@ 'not (list (-t.@ 'not (list t*)))) t*]
          [_ t]))
      (φs+ Γ t*)))

  (define (Γ++ [Γ : -Γ] [φs : -Γ]) : -Γ (apply Γ+ Γ (set->list φs)))

  (: σ⊕! : -Σ -Γ ⟪α⟫ -W¹ → Void)
  (define (σ⊕! Σ Γ ⟪α⟫ W)
    (match-define (-W¹ V t) W)
    (define V* (V+ (-Σ-σ Σ) V (predicates-of Γ t)))
    (σ⊕V! Σ ⟪α⟫ V*))  

  (: σ⊕V! : -Σ ⟪α⟫ -V → Void)
  (define (σ⊕V! Σ α V)
    (set--Σ-σ! Σ (σ⊕ (-Σ-σ Σ) α V)))

  (: σ⊕Vs! : -Σ ⟪α⟫ (℘ -V) → Void)
  (define (σ⊕Vs! Σ α Vs)
    (define σ*
      (hash-update (-Σ-σ Σ)
                   α
                   (λ ([Vs₀ : (℘ -V)])
                     (cond [(set-empty? Vs₀) Vs] ; fast special case
                           [else
                            (for/fold ([Vs* : (℘ -V) Vs₀])
                                      ([V (in-set Vs)])
                              (Vs⊕ (-Σ-σ Σ) Vs* V))]))
                   mk-∅))
    (set--Σ-σ! Σ σ*))

  (: σ-copy! : -Σ ⟪α⟫ ⟪α⟫ → Void)
  (define (σ-copy! Σ α-src α-tgt)
    (unless (equal? α-src α-tgt)
      (σ⊕Vs! Σ α-tgt (σ@ Σ α-src))))

  (: σ⊕ : -σ ⟪α⟫ -V → -σ)
  (define (σ⊕ σ α V)
    (match (⟪α⟫->-α α)
      ; TODO just debugging. Shouldn't happen
      [(-α.imm V*)
       (unless (equal? V V*)
         (error 'σ⊕ "illegal allocation: ~a ↦ ~a~n" (show-V V*) (show-V V)))
       σ]
      [_
       (hash-update σ α (λ ([Vs : (℘ -V)]) (Vs⊕ σ Vs V)) mk-∅)]))

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

  (: V+ : -σ -V (U -V -h (℘ -h)) → -V)
  ;; Refine opaque value with predicate
  (define (V+ σ V P)
    
    (define (simplify [P : -V]) : -V
      (match P
        [(-Ar _ (and α (app ⟪α⟫->-α (or (? -α.wrp?) (? -e?)))) _)
         (define Vs (σ@ σ α))
         (cond [(= 1 (set-count Vs)) (simplify (set-first Vs))]
               [else P])]
        [(-St/C _ 𝒾 _) (-st-p 𝒾)]
        [(or (? -Vectorof?) (? -Vector/C?)) 'vector?]
        [_ P]))
    
    (cond
      [(set? P)
       (for/fold ([V : -V V]) ([Pᵢ (in-set P)])
         (V+ σ V Pᵢ))]
      [else
       (with-debugging/off
         ((V*)
          (match V
            [(-● ps)
             (match P
               [(or (-≡/c b) (-b b)) (-b b)]
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

  (define φ+ : (-t -t → (Option -Γ))
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
           (define α₂ (ρ@ ρ₂ x))
           (or (and (-V? α₁) (-V? α₂) (go α₁ α₂))
               (and (not (-V? α₁)) (not (-V? α₂)) (go/⟪α⟫ α₁ α₂))))]
        [(_ _) #f]))

    (go V₁ V₂))

  (define (φs⊑ [φs₁ : -Γ] [φs₂ : -Γ]) : Boolean (⊆ φs₂ φs₁))

  (: Γ⊑ : -Γ -Γ → Boolean)
  (define (Γ⊑ Γ₁ Γ₂) (⊆ Γ₂ Γ₁))

  (define (?Γ⊔ [Γ₁ : -Γ] [Γ₂ : -Γ]) : (Option -Γ)
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

  (define (σₖ⊕! [Σ : -Σ] [αₖ : -αₖ] [κ : -κ]) : Void
    (set--Σ-σₖ! Σ (σₖ⊕ (-Σ-σₖ Σ) αₖ κ)))

  (define (σₖ⊕ [σₖ : -σₖ] [αₖ : -αₖ] [κ : -κ]) : -σₖ
    (hash-update σₖ αₖ (set-add/compact κ ?κ⊔) mk-∅))

  (: σₖ+! : -Σ -αₖ -κ → -αₖ)
  (define (σₖ+! Σ αₖ κ)
    (define Ξ (-Σ-Ξ Σ))
    (define-values (ctx pth) (αₖ->ctx+pth αₖ))
    (define pths₀ (hash-ref Ξ ctx mk-∅))
    (define ?pth
      (for/or : (U #f -αₖ:pth (℘ -αₖ:pth)) ([pth₀ (in-set pths₀)])
        (cond [(αₖ:pth⊑ pth pth₀) pth₀]
              [(αₖ:pth⊑ pth₀ pth)
               (for/set: : (℘ -αₖ:pth) ([pth₀* (in-set pths₀)]
                                        #:when (or (eq? pth₀* pth₀) (αₖ:pth⊑ pth₀* pth)))
                 pth₀*)]
              [else #f])))
    (define-values (pth* pths*)
      (cond
        [(set? ?pth) (values pth (set-add (set-subtract pths₀ ?pth) pth))]
        [(-αₖ:pth? ?pth) (values ?pth pths₀)]
        [else (values pth (set-add pths₀ pth))]))
    (define αₖ* (ctx+pth->αₖ ctx pth*))
    (set--Σ-Ξ! Σ (hash-set Ξ ctx pths*))
    (σₖ⊕! Σ αₖ* κ)
    αₖ*)

  (: αₖ:pth⊑ : -αₖ:pth -αₖ:pth → Boolean)
  (define αₖ:pth⊑
    (match-lambda**
     [((-αₖ:pth $₀ Γ₀) (-αₖ:pth $₁ Γ₁))
      (and ($⊑ $₀ $₁) (Γ⊑ Γ₀ Γ₁))]))

  (: $⊑ : -$ -$ → Boolean)
  (define ($⊑ $₀ $₁)
    (for/and : Boolean ([(l t) (in-hash $₁)])
      (equal? t (hash-ref $₀ l #f))))

  (: ?κ⊔ : -κ -κ → (Option -κ))
  (define (?κ⊔ κ₁ κ₂)

    (: t⊑ : -?t -?t → Boolean)
    (define (t⊑ t₁ t₂)
      (implies t₂ (equal? t₁ t₂)))

    (: κ⊑ : -κ.rt -κ.rt → Boolean)
    (define (κ⊑ κ₁ κ₂)
      (match-define (-κ.rt ⟦k⟧₁ dom₁ Γ₁ t₁ looped?₁) κ₁)
      (match-define (-κ.rt ⟦k⟧₂ dom₂ Γ₂ t₂ looped?₂) κ₂)
      (and (⟦k⟧₁ . equal? . ⟦k⟧₂)
           (dom₂ . ⊆  . dom₁)
           (Γ₂   . ⊆  . Γ₁)
           (t₁   . t⊑ . t₂)
           (looped?₁ . implies . looped?₂)))

    (match* (κ₁ κ₂)
      [((-κ.rt ⟦k⟧₁ dom₁ Γ₁ t₁ looped?₁)
        (-κ.rt ⟦k⟧₂ dom₂ Γ₂ t₂ looped?₂))
       (cond [(κ⊑ κ₁ κ₂) κ₂]
             [(κ⊑ κ₂ κ₁) κ₂]
             [(and (equal? ⟦k⟧₁ ⟦k⟧₂)
                   (t₁ . t⊑ . t₂)
                   (dom₂ . ⊆ . dom₁)
                   (looped?₁ . implies . looped?₂))
              (define ?Γ (?Γ⊔ Γ₁ Γ₂))
              (and ?Γ (-κ.rt ⟦k⟧₂ dom₂ ?Γ t₂ looped?₂))]
             [else #f])]
      [(κ κ) κ]
      [(_ _) #f]))

  (define (add-leak! [Σ : -Σ] [V : -V]) : Void
    (when (behavioral? (-Σ-σ Σ) V)
      (σ⊕V! Σ ⟪α⟫ₕᵥ V)))

  (: alloc-init-args! :
     -Σ -$ -Γ -ρ -⟪ℋ⟫ (Listof Symbol) (Listof -W¹) Boolean → (Values -ρ -$))
  (define (alloc-init-args! Σ $ Γ ρ ⟪ℋ⟫ xs Ws looped?)
    (define ρ* (ρ+ ρ -x-dummy (-α->⟪α⟫ (-α.fv ⟪ℋ⟫))))
    (bind-args! Σ $ Γ ρ* ⟪ℋ⟫ xs Ws looped?))

  (: bind-args! : -Σ -$ -Γ -ρ -⟪ℋ⟫ (Listof Symbol) (Listof -W¹) Boolean → (Values -ρ -$))
  (define (bind-args! Σ $ Γ ρ ⟪ℋ⟫ xs Ws looped?)
    (define σ (-Σ-σ Σ))
    (define-values (ρ* $* canon)
      (for/fold ([ρ : -ρ ρ] [$ : -$ $] [canon : (Immutable-HashTable -t Symbol) (hash)])
                ([x xs] [Wₓ Ws])
        (match-define (-W¹ Vₓ tₓ) Wₓ)
        (define Vₓ* (V+ σ Vₓ (predicates-of Γ tₓ)))
        (define-values (tₓ* canon*)
          (cond [(not tₓ) (values (-t.x x) canon)]
                [(not looped?) (values tₓ canon)]
                [(hash-ref canon tₓ #f) => (λ ([y : Symbol]) (values (-t.x y) canon))]
                [else (values (-t.x x) (hash-set canon tₓ x))]))
        (define α (hash-ref ρ x #|in case of letrec|#
                            (λ () (-α->⟪α⟫ (-α.x x ⟪ℋ⟫ (predicates-of-V Vₓ*))))))
        (σ⊕V! Σ α Vₓ*)
        (define $* (if tₓ* ($-set $ x tₓ*) $))
        (values (ρ+ ρ x α) $* canon*)))
    (values ρ* $*))

  (: alloc-rest-args! ([-Σ -Γ -⟪ℋ⟫ ℓ (Listof -W¹)] [#:end -V] . ->* . -V))
  (define (alloc-rest-args! Σ Γ ⟪ℋ⟫ ℓ Ws #:end [Vₙ -null])

    (: precise-alloc! ([(Listof -W¹)] [Natural] . ->* . -V))
    ;; Allocate vararg list precisely, preserving length
    (define (precise-alloc! Ws [i 0])
      (match Ws
        [(list) Vₙ]
        [(cons Wₕ Ws*)
         (define αₕ (-α->⟪α⟫ (-α.var-car ℓ ⟪ℋ⟫ i)))
         (define αₜ (-α->⟪α⟫ (-α.var-cdr ℓ ⟪ℋ⟫ i)))
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
       (define αₕ (-α->⟪α⟫ (-α.var-car ℓ ⟪ℋ⟫ #f)))
       (define αₜ (-α->⟪α⟫ (-α.var-cdr ℓ ⟪ℋ⟫ #f)))
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
        [(-● ps) #:when (∋ ps 'list?) {set (arity-at-least 0)}]
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
           [(-● ps) #:when (∋ ps 'list?)
            {set (cons (make-list n (+●)) (+● 'list?))}]
           [_ ∅])])))

  (: M⊕! : -Σ -αₖ -ΓA → Void)
  (define (M⊕! Σ αₖ ΓA)
    (set--Σ-M! Σ (hash-update (-Σ-M Σ) αₖ (λ ([ans : (℘ -ΓA)]) (set-add ans ΓA)) mk-∅)))

  (: copy-Γ : (℘ Symbol) -Γ -Γ → -Γ)
  (define (copy-Γ dom Γₜ Γₛ)
    (∪ Γₜ (Γ↓ Γₛ dom)))
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
