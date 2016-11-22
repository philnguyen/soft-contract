#lang typed/racket/base

(provide σ⊕! σ⊕*! V+ Vs⊕
         extract-list-content)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "local.rkt"
         (for-syntax racket/base racket/list racket/syntax syntax/parse))

(: σ⊕! ([-σ -⟪α⟫ -V] [#:mutating? Boolean] . ->* . Void))
(define (σ⊕! σ α V #:mutating? [mutating? #f])
  (match-define (-σ m mods crds) σ)
  (define Vs*
    (cond
      ;; If address only stands for 1 value and this is the first update, do strong update.
      ;; This gives some precision for programs that initialize `(box #f)`
      ;; then update it with fairly type-consistent values afterwards
      [(and mutating?
            (not (hash-has-key? mods α))
            (not (equal? 'N (hash-ref crds α (λ () 0)))))
       (hash-set! crds α 1)
       {set V}]
      [else
       (define Vs (hash-ref m α →∅))
       (hash-update! crds α cardinality+ (λ () 0))
       (Vs⊕ σ Vs V)]))
  (hash-set! m α Vs*)
  (when mutating?
    (hash-set! mods α #t))
  (when (-α.vct? α)
    (printf "widening vector content at ~a with ~a to ~a~n"
            (show-⟪α⟫ α)
            (show-V V)
            (set-map Vs* show-V))))

(define-syntax σ⊕*!
  (syntax-rules (↦)
    [(_ σ) (void)]
    [(_ σ [α ↦ V] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕!  σ (ann α -⟪α⟫) V #:mutating? #f)
       (σ⊕*! σ p ...))]
    [(_ σ [α ↦ V #:mutating? b?] p ...)
     (begin ; FIXME the annotation is to work around TR bug
       (σ⊕!  σ (ann α -⟪α⟫) V b?)
       (σ⊕*! σ p ...))]))

(: V⊑ : -σ -V -V → Boolean)
;; Check if `V₂` definitely subsumes `V₁`
;; `#f` is a conservative "don't know" answer
(define (V⊑ σ V₁ V₂)

  (define-set seen : (Pairof -⟪α⟫ -⟪α⟫) #:as-mutable-hash? #t)

  (: go/⟪α⟫ : -⟪α⟫ -⟪α⟫ → Boolean)
  (define (go/⟪α⟫ α₁ α₂)
    (define α₁α₂ (cons α₁ α₂))
    (cond
      [(seen-has? α₁α₂) #t]
      [else
       (seen-add! α₁α₂)
       (define Vs₁ (σ@ σ α₁))
       (define Vs₂ (σ@ σ α₂))
       (for/and : Boolean ([V₁ Vs₁])
         (for/or : Boolean ([V₂ Vs₂])
           (go V₁ V₂)))]))

  (: go : -V -V → Boolean)
  (define (go V₁ V₂)
    (match* (V₁ V₂)
      [(V V) #t]
      [(_ (-● ps)) #:when (not (behavioral? σ V₁))
       (for/and : Boolean ([p ps])
         (equal? '✓ (p∋Vs σ p V₁)))]
      [((-St 𝒾 αs₁) (-St 𝒾 αs₂)) #:when (struct-all-immutable? 𝒾)
       (for/and : Boolean ([α₁ : -⟪α⟫ αs₁] [α₂ : -⟪α⟫ αs₂])
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
      [(-Ar _ (and α (app -⟪α⟫->-α (or (? -α.def?) (? -α.wrp?) (? -e?)))) _)
       (define Vs (σ@ σ α))
       (cond [(= 1 (set-count Vs)) (simplify (set-first Vs))]
             [else P])]
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

(: p+ : -v -v → (Option (℘ -v)))
;; Combine 2 predicates for a more precise one.
;; Return `#f` if there's no single predicate that refines both
(define p+
  (let-syntax ([match-lambda**/symmetry
                ;; b/c TR doesn't work well with `match-lambda*` and `list-no-order`
                (syntax-parser
                  [(_ clauses ...)
                   (define doubled-clauses
                     (append-map
                      (λ (clause)
                        (with-syntax ([[(x y) e ...] clause])
                          (list #'[(x y) e ...] #'[(y x) e ...])))
                      (syntax->list #'(clauses ...))))
                   #`(match-lambda** #,@doubled-clauses [(_ _) #f])])])
    
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
     [('list? (-not/c 'null?)) {set 'list? -cons?}]
     [('list? (-not/c -cons?)) {set 'null?}])))

(: ps+ : (℘ -v) -v → (℘ -v))
;; Strengthen refinement set with new predicate
(define (ps+ ps p)

  (: iter : (℘ -v) -v → (U (℘ -v) (Pairof (℘ -v) (℘ -v))))
  (define (iter ps p)
    (match (for/or : (Option (List (℘ -v) -v -v)) ([pᵢ ps])
             (cond [(p+ pᵢ p) => (λ ([ps : (℘ -v)]) (list ps pᵢ p))]
                   [else #f]))
      [(list ps pᵢ p)
       (cons (set-remove (set-remove ps pᵢ) p)
             ps)]
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

(: V⊕ : -σ -V -V → (Option -V))
;; Widen 2 values to one approximating both.
;; Return `#f` if no approximation preferred
(define (V⊕ σ V₁ V₂)
  (match* (V₁ V₂)
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
      char? boolean?)]
    [((-b 0) (-● ps))
     (define p
       (for/or : (Option -v) ([p ps])
         (match p
           [(->/c 0) p]
           [(-</c 0) p]
           [_ #f])))
     (and p (-● (set-remove ps p)))]
    [((-● ps) (-● qs)) (-● (∩ ps qs))]
    [(_ _) #f]))



(: extract-list-content : -σ -St → (℘ -V))
;; Return an abstract value approximating all list element in `V`
(define (extract-list-content σ V)
  (define-set seen : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-Cons αₕ αₜ) V)
  (define Vs (σ@ σ αₕ))
  (let loop! ([αₜ : -⟪α⟫ αₜ])
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
