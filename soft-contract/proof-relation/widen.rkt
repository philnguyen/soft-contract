#lang typed/racket/base

(provide σ⊕! σ⊕*! σ⊕V! σ⊕V*! Vs⊕
         M⊕ M⊕!
         σₖ⊕!
         Γ+ Γ++ V+
         predicates-of-W
         inv-caller->callee inv-callee->caller
         extract-list-content)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "local.rkt"
         (for-syntax racket/base racket/list racket/syntax syntax/parse))

(: Γ+ : -Γ -?t * → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ . ts)
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

(: Γ++ : -Γ (℘ -t) → -Γ)
(define (Γ++ Γ φs) (apply Γ+ Γ (set->list φs)))

(: σ⊕! ([-Σ -Γ ⟪α⟫ -W¹] [#:mutating? Boolean] . ->* . Void))
(define (σ⊕! Σ Γ ⟪α⟫ W #:mutating? [mutating? #f])
  (match-define (-W¹ V s) W)
  (σ⊕V! Σ ⟪α⟫ (V+ (-Σ-σ Σ) V (predicates-of Γ s)) #:mutating? mutating?))

(define-syntax σ⊕*!
  (syntax-rules (↦)
    [(_ Σ Γ) (void)]
    [(_ Σ Γ [α ↦ V] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕!  Σ Γ (ann α ⟪α⟫) V #:mutating? #f)
       (σ⊕*! Σ Γ p ...))]
    [(_ Σ [α ↦ V #:mutating? b?] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕!  Σ Γ (ann α ⟪α⟫) V b?)
       (σ⊕*! Σ Γ p ...))]))

(: σ⊕V! ([-Σ ⟪α⟫ -V] [#:mutating? Boolean] . ->* . Void))
(define (σ⊕V! Σ α V #:mutating? [mutating? #f])
  (match-define (-Σ σ _ _) Σ)
  (set--Σ-σ! Σ (σ⊕ σ α V mutating?)))

(define-syntax σ⊕V*!
  (syntax-rules (↦)
    [(_ Σ) (void)]
    [(_ Σ [α ↦ V] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕V!  Σ (ann α ⟪α⟫) V #:mutating? #f)
       (σ⊕V*! Σ p ...))]
    [(_ Σ [α ↦ V #:mutating? b?] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕V!  Σ (ann α ⟪α⟫) V b?)
       (σ⊕V*! Σ p ...))]))

(: σ⊕ : -σ ⟪α⟫ -V Boolean → -σ)
(define (σ⊕ σ α V mutating?)
  (match-define (-σ m mods crds) σ)
  (begin ; just for debugging
    (define Vs₀ (hash-ref m α →∅))
    (define modified?₀ (∋ mods α))
    (define crd₀ (hash-ref crds α (λ () 0))))
  (define-values (Vs* crds*)
    (cond
      ;; If address only stands for 1 value and this is the first update, do strong update.
      ;; This gives some precision for programs that initialize `(box #f)`
      ;; then update it with fairly type-consistent values afterwards
      [(and mutating?
            (not (∋ mods α))
            (not (equal? 'N (hash-ref crds α (λ () 0)))))
       (values {set V} (hash-set crds α 1))]
      [else
       (define Vs (hash-ref m α →∅))
       (define crds*
         (match (⟪α⟫->-α α)
           [(? -𝒾?) ; can't bind top-level from 2 places
            (hash-set crds α
                      (case crd₀
                        [(0) 1]
                        [(1) 1]
                        [(N) 'N]))]
           [_ (hash-update crds α cardinality+ (λ () 0))]))
       (values (Vs⊕ σ Vs V) crds*)]))
  (define m* (hash-set m α Vs*))
  (define mods* (if mutating? (set-add mods α) mods))

  #;(when (∋ Vs* (-● ∅))
    (printf "~a : ~a ⊕ ~a -> ~a~n"
            (show-⟪α⟫ α)
            (set-map Vs₀ show-V)
            (show-V V)
            (set-map Vs* show-V)))
  
  (-σ m* mods* crds*))

(: Vs⊕ : -σ (℘ -V) -V → (℘ -V))
;; Widen value set with new value
(define (Vs⊕ σ Vs V)
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

  (repeat-compact Vs V iter))

(: V+ : -σ -V (U -V -h (℘ -h)) → -V)
;; Refine opaque value with predicate
(define (V+ σ V P) : -V
  
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

(: p+ : -h -h → (Option (℘ -h)))
;; Combine 2 predicates for a more precise one.
;; Return `#f` if there's no single predicate that refines both
(define p+
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

(: ps+ : (℘ -h) -h → (℘ -h))
;; Strengthen refinement set with new predicate
(define (ps+ ps p)

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

(: φs+ : (℘ -t) -t → (℘ -t))
(define (φs+ φs φ)
  
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

(: φ+ : -t -t → (Option (℘ -t)))
(define φ+
  (match-lambda**/symmetry ; FIXME inefficiency, there's no e⊢e
   [(φ ψ) #:when (equal? '✓ (φs⊢t {set φ} ψ)) {set φ}]
   [(_ _) #f]))

(: V⊕ : -σ -V -V → (Option -V))
;; Widen 2 values to one approximating both.
;; Return `#f` if no approximation preferred
(define (V⊕ σ V₁ V₂)
  (with-debugging ((V*) (match* (V₁ V₂)
                          [(_ _) #:when (V⊑ σ V₂ V₁) V₁]
                          [(_ _) #:when (V⊑ σ V₁ V₂) V₂]
                          ; TODO more heuristics
                          [((-b b₁) (-b b₂)) #:when (not (equal? b₁ b₂))
                           (cond
                             ;; Handle non-null `char?` specially to retain `path-string?`-ness elsewhere
                             #;[(and (char? b₁) (char? b₂) (not (equal? #\null b₁)) (not (equal? #\null b₂)))
                              (-● {set 'char? (-not/c (-≡/c #\null))})]
                             [else
                              (define-syntax-rule (check-for-base-types p? ...)
                                (cond
                                  [(and (p? b₁) (p? b₂)) (-● {set 'p?})] ...
                                  [else #f]))

                              (check-for-base-types
                               exact-positive-integer? exact-nonnegative-integer? exact-integer?
                               integer? real? number?
                               path-string? string?
                               char? boolean?)])]
                          [((-b 0) (-● ps))
                           (define p
                             (for/or : (Option -h) ([p ps])
                               (match p
                                 [(->/c 0) p]
                                 [(-</c 0) p]
                                 [_ #f])))
                           (and p (-● (set-remove ps p)))]
                          [((-● ps) (-● qs))
                           (define ps* (ps⊕ ps qs))
                           (if (set-empty? ps*) #|just a heuristic|# #f (-● ps*))]
                          [(_ _) #f]))
    (when (or (let ([●? (λ (V) (and (-V? V) (equal? V (-● ∅))))])
                (and (●? V*) (not (●? V₁)) (not (●? V₂)))))
      (printf "Warning: ~a ⊕ ~a = ~a~n~n" (show-V V₁) (show-V V₂) (show-V V*)))))

(: ps⊕ : (℘ -h) (℘ -h) → (℘ -h))
;; Return refinement set that's an over-approximation of both sets
(define (ps⊕ ps₁ ps₂)
  (for*/union : (℘ -h) ([p₁ ps₁] [p₂ ps₂]) (p⊕ p₁ p₂)))

(: p⊕ : -h -h → (℘ -h))
;; Return predicate that's weaker than both
(define p⊕
  (match-lambda**/symmetry
   [(p q) #:when (equal? '✓ (p⇒p q p)) {set p}]
   [(_ _) ∅]))

(: extract-list-content : -σ -St → (℘ -V))
;; Return an abstract value approximating all list element in `V`
(define (extract-list-content σ V)
  (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-Cons αₕ αₜ) V)
  (define Vs (σ@ σ αₕ))
  (let loop! ([αₜ : ⟪α⟫ αₜ])
    (unless (seen-has? αₜ)
      (seen-add! αₜ)
      (for ([Vₜ (σ@ σ αₜ)])
        (match Vₜ
          [(-Cons αₕ* αₜ*)
           (for ([Vₕ (σ@ σ αₕ*)])
             (set! Vs (Vs⊕ σ Vs Vₕ)))
           (loop! αₜ*)]
          [(-b (list)) (void)]
          [_ (set! Vs (Vs⊕ σ Vs (-● ∅)))]))))
  Vs)

(: V⊑ : -σ -V -V → Boolean)
;; Check if `V₂` definitely subsumes `V₁`
;; `#f` is a conservative "don't know" answer
(define (V⊑ σ V₁ V₂)

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

(: φs⊑ : (℘ -t) (℘ -t) → Boolean)
(define (φs⊑ φs₁ φs₂) (⊆ φs₂ φs₁))

(: Γ⊑ : -Γ -Γ → Boolean)
(define (Γ⊑ Γ₁ Γ₂)
  (match-define (-Γ φs₁ _) Γ₁)
  (match-define (-Γ φs₂ _) Γ₂)
  (⊆ φs₂ φs₁))

(: ΓA⊑ : -σ → -ΓA -ΓA → Boolean)
(define ((ΓA⊑ σ) ΓA₁ ΓA₂)
  (match-define (-ΓA Γ₁ A₁) ΓA₁)
  (match-define (-ΓA Γ₂ A₂) ΓA₂)
  (and (φs⊑ Γ₁ Γ₂) (A⊑ σ A₁ A₂)))

(: ?Γ⊔ : (℘ -t) (℘ -t) → (Option (℘ -t)))
(define (?Γ⊔ Γ₁ Γ₂)
  (define-values (Γ* δΓ₁ δΓ₂) (set-intersect/differences Γ₁ Γ₂))
  (cond [(and (= 1 (set-count δΓ₁))
              (= 1 (set-count δΓ₂)))
         (define φ₁ (set-first δΓ₁))
         (define φ₂ (set-first δΓ₂))
         (cond [(complement? φ₁ φ₂) Γ*]
               [(φs⊢t {set φ₁} φ₂) Γ₂]
               [(φs⊢t {set φ₂} φ₁) Γ₁]
               [else #f])]
        [else #f]))

(: ?ΓA⊔ : -σ → -ΓA -ΓA → (Option -ΓA))
(define ((?ΓA⊔ σ) ΓA₁ ΓA₂)
  (cond [((ΓA⊑ σ) ΓA₁ ΓA₂) ΓA₂]
        [((ΓA⊑ σ) ΓA₂ ΓA₁) ΓA₁]
        [else
         (match-define (-ΓA Γ₁ A₁) ΓA₁)
         (match-define (-ΓA Γ₂ A₂) ΓA₂)
         (define ?Γ (and (equal? A₁ A₂) (?Γ⊔ Γ₁ Γ₂)))
         (and ?Γ (-ΓA ?Γ A₂))]))

(: M⊕ : -M -σ -αₖ (℘ -t) -A → -M)
(define (M⊕ M σ αₖ Γ A)
  (hash-update M αₖ (set-add/compact (-ΓA Γ A) (?ΓA⊔ σ)) →∅))

(: M⊕! : -Σ -αₖ (℘ -t) -A → Void)
(define (M⊕! Σ αₖ Γ A)
  (match-define (-Σ σ _ M) Σ)
  (set--Σ-M! Σ (M⊕ M σ αₖ Γ A)))

(: σₖ⊕! : -Σ -αₖ -κ → Void)
(define (σₖ⊕! Σ αₖ κ)
  (match-define (-Σ _ σₖ _) Σ)
  (set--Σ-σₖ! Σ (σₖ⊕ σₖ αₖ κ)))

(: σₖ⊕ : -σₖ -αₖ -κ → -σₖ)
(define (σₖ⊕ σₖ αₖ κ)
  (define (κ⊑ [κ₁ : -κ] [κ₂ : -κ])
    (match-define (-κ ⟦k⟧₁ Γ₁ ⟪ℋ⟫₁ sₓs₁) κ₁)
    (match-define (-κ ⟦k⟧₂ Γ₂ ⟪ℋ⟫₂ sₓs₂) κ₂)
    (and (equal? ⟦k⟧₁ ⟦k⟧₂)
         (equal? ⟪ℋ⟫₁ ⟪ℋ⟫₂)
         (equal? sₓs₁ sₓs₂)
         (Γ⊑ Γ₁ Γ₂)))

  (hash-update σₖ αₖ (set-add/remove-redundant κ κ⊑) →∅))

(: predicates-of-W : -σ -Γ -W¹ → (℘ -h))
;; Extract predicates of `W`'s symbol that are not already implied by `W`'s value
(define (predicates-of-W σ Γ W)
  (match-define (-W¹ V t) W)
  (define ps₁
    (match V
      [(-● ps) ps]
      [(-St 𝒾 _) {set (-st-p 𝒾)}]
      [(-St* (-St/C _ 𝒾 _) _ _) {set (-st-p 𝒾)}]
      [_ ∅]))
  (define ps₂
    (for/set: : (℘ -h) ([p (predicates-of Γ t)]
                        #:unless (and #|HACK|# (-●? V) (equal? '✓ (p∋Vs σ p V))))
      p))

  #;(printf "predicates-of ~a in ~a: ~a ∪ ~a~n"
          (show-W¹ W) (show-Γ Γ) (set-map φs show-t) (set-map ψs show-t))
  
  (∪ ps₁ ps₂))

(: inv-caller->callee : -σ (℘ Symbol) -formals (Listof -W¹) -Γ -Γ → -Γ)
;; Convert invariants about arguments in caller into those about parameters in callee
(define (inv-caller->callee σ fvs fml Ws Γₑᵣ Γₑₑ)

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

(: accum-aliases : (HashTable Symbol -t) -formals (Listof -?t) → (HashTable Symbol -t))
(define (accum-aliases as fml args)

  (define xs : (Listof Symbol)
    (match fml
      [(? list? xs) xs]
      [(-var xs _ ) xs]))

  ;; specific hack just for `octy/ex-{08,12}.rkt`, `mochi/intro3.rkt`
  (define (restrictedly-occured? [t : -t])
    (with-debugging/off ((res?) (for/or : Boolean ([(x₀ t₀) (in-hash as)])
      (match? t (-t.@ (? h-unique?) (or (list (== t₀))
                                        (list (== t₀) (? -b?)))))))
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

(: inv-callee->caller : -σ (℘ Symbol) -formals (Listof -?t) -Γ -Γ → -Γ)
;; Propagate simple predicate back to caller
(define (inv-callee->caller σ fvs fml ts Γₑᵣ Γₑₑ)
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
    (∪ φsₑᵣ
       (for*/set: : (℘ -t) ([φ (in-set φsₑₑ)]
                            [φ* (in-value (ee->er φ))] #:when φ*)
         φ*)))

  #;(begin
    (printf "inv-callee->caller: ~a ↦ ~a~n" fml (map show-t ts))
    (printf "  - ee : ~a~n" (set-map φsₑₑ  show-t))
    (printf "  - er : ~a~n" (set-map φsₑᵣ  show-t))
    (printf "  - er*: ~a~n" (set-map φsₑᵣ* show-t))
    (printf "~n"))

  (-Γ φsₑᵣ* asₑᵣ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; HELPERS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

