#lang typed/racket/base

(provide σ⊕! σ⊕*! σ⊕V! σ⊕V*! Vs⊕
         M⊕ M⊕!
         Γ+ Γ++ V+
         predicates-of-W
         inv-caller->callee
         extract-list-content)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "local.rkt"
         (for-syntax racket/base racket/list racket/syntax syntax/parse))

(: Γ+ : -Γ -s * → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ . ss)
  (match-define (-Γ φs as ts) Γ)
  (define φs*
    (for/fold ([φs : (℘ -e) φs]) ([s ss]
                                  #:when s
                                  #:unless (set-empty? (fv s)))
      (φs+ φs s)))
  (-Γ φs* as ts))

(: Γ++ : -Γ (℘ -e) → -Γ)
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

(: V+ : -σ -V (U -v -V (℘ -v) (℘ -V)) → -V)
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
             [(-≡/c (? -V? V*)) #:when V* V*]
             ['not -ff]
             ['null? -null]
             ['void? -void]
             [(? -v? v) (-● (ps+ ps v))]
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

(: p+ : -v -v → (Option (℘ -v)))
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
   [('exact-nonnegative-integer? (-not/c (-=/c 0)))
    {set 'exact-positive-integer?}]
   [('exact-nonnegative-integer? (-≠/c 0))
    {set 'exact-positive-integer?}]
   [('list? (-not/c 'null?)) {set 'list? -cons?}]
   [('list? (-not/c -cons?)) {set 'null?}]
   [(_ _) #f]))

(: ps+ : (℘ -v) -v → (℘ -v))
;; Strengthen refinement set with new predicate
(define (ps+ ps p)

  (: iter : (℘ -v) -v → (U (℘ -v) (Pairof (℘ -v) (℘ -v))))
  (define (iter ps p)
    (match (for/or : (Option (List (℘ -v) -v -v)) ([pᵢ ps])
             (cond [(p+ pᵢ p) => (λ ([ps* : (℘ -v)]) (list ps* pᵢ p))]
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

  (repeat-compact ps p iter))

(: φs+ : (℘ -e) -e → (℘ -e))
(define (φs+ φs φ)
  
  (: iter : (℘ -e) -e → (U (℘ -e) (Pairof (℘ -e) (℘ -e))))
  (define (iter φs φ)
    (match (for/or : (Option (List (℘ -e) -e -e)) ([φᵢ φs])
             (cond [(φ+ φᵢ φ) => (λ ([φs* : (℘ -e)]) (list φs* φᵢ φ))]
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

(: φ+ : -e -e → (Option (℘ -e)))
(define φ+
  (match-lambda**/symmetry ; FIXME inefficiency, there's no e⊢e
   [(φ ψ) #:when (equal? '✓ (φs⊢e {set φ} ψ)) {set φ}]
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
       [(and (char? b₁) (char? b₂) (not (equal? #\null b₁)) (not (equal? #\null b₂)))
        (-● {set 'char? (-not/c (-≡/c (-b #\null)))})]
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
       (for/or : (Option -v) ([p ps])
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

(: ps⊕ : (℘ -v) (℘ -v) → (℘ -v))
;; Return refinement set that's an over-approximation of both sets
(define (ps⊕ ps₁ ps₂)
  (for*/union : (℘ -v) ([p₁ ps₁] [p₂ ps₂]) (p⊕ p₁ p₂)))

(: p⊕ : -v -v → (℘ -v))
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

(: Γ⊑ : -Γ -Γ → Boolean)
(define (Γ⊑ Γ₁ Γ₂)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (match-define (-Γ φs₂ _ γs₂) Γ₂)
  (and (⊆ φs₂ φs₁) (⊆ (list->set γs₂) (list->set γs₁))))

(: ΓA⊑ : -σ -ΓA -ΓA → Boolean)
(define (ΓA⊑ σ ΓA₁ ΓA₂)
  (match-define (-ΓA Γ₁ A₁) ΓA₁)
  (match-define (-ΓA Γ₂ A₂) ΓA₂)
  (and (Γ⊑ Γ₁ Γ₂) (A⊑ σ A₁ A₂)))

(: M⊕ : -M -σ -αₖ -Γ -A → -M)
(define (M⊕ M σ αₖ Γ A)
  #;(hash-update M αₖ (λ ([ΓAs : (℘ -ΓA)]) (set-add ΓAs (-ΓA Γ A))) →∅)
  (define ΓA (-ΓA Γ A))
  (hash-update M αₖ
               (λ ([ΓAs : (℘ -ΓA)])
                 (define-set subsumed-olds : -ΓA)
                 (define redundant? : Boolean #f)
                 (for ([ΓAᵢ (in-set ΓAs)])
                   (cond
                     [(ΓA⊑ σ ΓAᵢ ΓA) (subsumed-olds-add! ΓAᵢ)]
                     [(ΓA⊑ σ ΓA ΓAᵢ) (set! redundant? #t)]
                     [else (void)]))
                 (cond
                   [redundant? ΓAs]
                   [else (set-add (set-subtract ΓAs subsumed-olds) ΓA)]))
                →∅))

(: M⊕! : -Σ -αₖ -Γ -A → Void)
(define (M⊕! Σ αₖ Γ A)
  (match-define (-Σ σ _ M) Σ)
  (set--Σ-M! Σ (M⊕ M σ αₖ Γ A)))

(: predicates-of-W : -σ -Γ -W¹ → (℘ -v))
;; Extract predicates of `W`'s symbol that are not already implied by `W`'s value
(define (predicates-of-W σ Γ W)
  (match-define (-W¹ V s) W)
  (define φs
    (match V
      [(-● ps) ps]
      [_ ∅]))
  (with-debugging/off ((res) (for/set: : (℘ -v) ([φ (predicates-of Γ s)]
                      #:unless (equal? '✓ (p∋Vs σ φ V)))
    φ))
    (printf "predicates-of ~a in ~a: ~a~n" (show-W¹ W) (show-Γ Γ) (set-map res show-e))))

(: inv-caller->callee : -σ (℘ Symbol) -formals (Listof -W¹) -Γ → (℘ -e))
;; Convert invariants about arguments in caller into those about parameters in callee
(define (inv-caller->callee σ fvs fml Ws Γₑᵣ)

  (define xs : (Listof Symbol)
    (match fml
      [(? list? xs) xs]
      [(-var xs _ ) xs]))

  (define-values (arg->x x->V)
    (for/fold ([arg->x : (HashTable -e Symbol) (hash)]
               [x->V : (HashTable Symbol -V) (hasheq)])
              ([x xs] [W Ws]
               #:when (-W¹-s W)
               #:unless (hash-has-key? arg->x (-W¹-s W)))
      (values (hash-set arg->x (-W¹-s W) x)
              (hash-set x->V x (-W¹-V W)))))

  (define er->ee : (-e → (Option -e))
    (match-lambda
      [arg #:when (hash-has-key? arg->x arg) (-x (hash-ref arg->x arg))]
      [(-@ f xs ℓ)
       (define f* (er->ee f))
       (define xs* (map er->ee xs))
       (and f* (andmap -e? xs*) (-@ f* xs* ℓ))]
      [(? -prim? b) b]
      [(? -𝒾? 𝒾) 𝒾]
      [(and e (-x x)) #:when (∋ fvs x) e]
      [_ #f]))

  (define (redundant? [e : -e])
    (match e
      [(-@ (? -o? o) (list (-x x)) _)
       (cond [(hash-ref x->V x #f) =>
              (λ ([V : -V])
                (equal? '✓ (p∋Vs σ o V)))]
             [else #f])]
      [_ #f]))

  (with-debugging ((ans) (for*/set: : (℘ -e) ([e (in-set (-Γ-facts Γₑᵣ))]
                                                  [e* (in-value (er->ee e))]
                                                  #:when e*
                                                  #:unless (redundant? e*))
                               e*))
    (printf "caller->callee~n")
    (for ([x xs] [W Ws])
      (printf "  - ~a ↦ ~a~n" x (show-W¹ W)))
    (printf "caller: ~a~n" (show-Γ Γₑᵣ))
    (printf "callee: ~a~n~n" (set-map ans show-e))))

;; FIXME code dup
(: inv-callee->caller : (℘ Symbol) -formals (Listof -s) -Γ → (℘ -e))
;; Convert invariants about parameters in callee into ones about arguments in caller
(define (inv-callee->caller fvs fml args Γₑₑ)
  (define xs : (Listof Symbol)
    (match fml
      [(? list? xs) xs]
      [(-var xs _) xs]))
  
  (define x->arg
    (for/hasheq : (HashTable Symbol -e) ([x xs] [arg args] #:when arg)
      (values x arg)))
  
  (define ee->er : (-e → (Option -e))
    (match-lambda
      [(-x x) #:when (hash-has-key? x->arg x) (hash-ref x->arg x)]
      [(and e (-x x)) #:when (∋ fvs x) e]
      [(-@ f xs ℓ)
       (define f* (ee->er f))
       (define xs* (map ee->er xs))
       (and f* (andmap -e? xs*) (-@ f* xs* ℓ))]
      [(? -prim? p) p]
      [(? -𝒾? 𝒾) 𝒾]
      [_ #f]))
  
  (with-debugging/off ((ans) (for*/set: : (℘ -e) ([e (in-set (-Γ-facts Γₑₑ))]
                                              [e* (in-value (ee->er e))] #:when e*)
                           e*))
    (printf "callee->caller~n")
    (for ([x xs] [arg args])
      (printf "  - ~a ↦ ~a~n" x (show-s arg)))
    (printf "callee: ~a~n" (show-Γ Γₑₑ))
    (printf "caller: ~a~n~n" (set-map ans show-e))))


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
