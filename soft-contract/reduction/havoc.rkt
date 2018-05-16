#lang typed/racket/base

(provide havoc@)

(require racket/match
         racket/set
         racket/list
         racket/sequence
         racket/splicing
         racket/bool
         typed/racket/unit
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit havoc@
  (import static-info^
          val^ sto^ evl^ for-gc^
          prover^
          alloc^ app^ step^ approx^)
  (export havoc^) 
  
  (: gen-havoc-expr : ((Listof -module) → -e))
  (define (gen-havoc-expr ms)
    (define refs
      (for*/list : (Listof -x) ([m (in-list ms)]
                                [path (in-value (-module-path m))]
                                [form (in-list (-module-body m))] #:when (-provide? form)
                                [spec (in-list (-provide-specs form))] #:when (-p/c-item? spec))
        (match-define (-p/c-item x _ _) spec)
        (-x (-𝒾 x path) (loc->ℓ (loc 'top-level-havoc 0 0 (list x))))))
    (-@ (-•) refs (loc->ℓ (loc 'havoc-expr 0 0 '()))))
  
  (: add-leak! : ((U HV-Tag α) Σ V^ → Void))
  (define (add-leak! tag Σ V)
    (define (keep-behavioral [V : V^]) : V^
      (for/fold ([V : V^ V])
                ([Vᵢ (in-set V)] #:unless (behavioral? (Σ-val Σ) Vᵢ))
        (set-remove V Vᵢ)))
    (define leaks
      (cond [(set? V) (keep-behavioral V)]
            [else
             (for/fold ([V : V^ ∅]) ([Vᵢ (in-list V)])
               (∪ V (keep-behavioral Vᵢ)))]))
    (⊔ᵥ! Σ (if (pair? tag) (tag->leak tag) tag) leaks))

  (: havoc : HV-Tag R^ Ξ:co Σ → (℘ Ξ))
  (define (havoc tag R^ Ξ₀ Σ)
    (define α• (tag->leak tag))
    (define Φ^ (collapse-R^/Φ^ R^))
    (for* ([Rᵢ (in-set R^)] [T (in-list (R-_0 Rᵢ))])
      (add-leak! α• Σ (T->V Σ Φ^ T)))
    (for/union : (℘ Ξ) ([V (in-set (Σᵥ@ Σ α•))] #:unless (seen? V (Σ-val Σ)))
       (havoc-V V Φ^ Ξ₀ Σ)))

  (: havoc-V : V Φ^ Ξ:co Σ → (℘ Ξ))
  (define (havoc-V V Φ^ Ξ₀ Σ)
    (match V
      ;; Apply function to appropriate number of arguments
      [(or (? Clo?) (? Case-Clo?) (X/G _ (? Fn/C?) _))
       (define with : ((U Natural arity-at-least) → (℘ Ξ))
         (match-lambda
           [(? index? k)
            (define args (make-list k {set (-● ∅)}))
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'app k))))
            ((app₁ V) args ℓ Φ^ Ξ₀ Σ)]
           [(arity-at-least n)
            (define Wᵢ (make-list n {set (-● ∅)}))
            (define Vᵣ {set (-● {set 'list?})})
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'app 'varargs))))
            ((app₁ 'apply) `(,{set V} ,@Wᵢ ,Vᵣ) ℓ Φ^ Ξ₀ Σ)]))
       (match (T-arity V)
         [(? list? ks)
          (for/union : (℘ Ξ) ([k (in-list ks)])
            (cond [(integer? k) (with k)]
                  [else (error 'havoc "TODO: arity ~a" k)]))]
         [(and k (or (? index?) (? arity-at-least?))) (with k)])]
      ;; Havoc and widen struct's publie fields
      [(or (St 𝒾 _) (X/G _ (St/C _ 𝒾 _) _))
       #:when 𝒾
       (define ℓ₁ (loc->ℓ (loc 'havoc 0 0 (list 'struct-ref (-𝒾-name 𝒾)))))
       (define ℓ₂ (loc->ℓ (loc 'havoc 0 0 (list 'struct-set! (-𝒾-name 𝒾)))))
       (∪ (for/union : (℘ Ξ) ([acc (get-public-accs 𝒾)])
            ((app₁ acc) (list {set V}) ℓ₁ Φ^ Ξ₀ Σ))
          (for/union : (℘ Ξ) ([mut (get-public-muts 𝒾)])
            ((app₁ mut) (list {set V} {set (-● ∅)}) ℓ₂ Φ^ Ξ₀ Σ)))]
      ;; Havoc vector's content before erasing it with unknowns
      [(X/G _ (or (? Vectof?) (? Vect/C?)) _)
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(vector-ref/guard))))
       (define Idx {set (-● {set 'exact-nonnegative-integer?})})
       (∪ ((app₁ 'vector-ref) (list {set V} Idx) ℓ Φ^ Ξ₀ Σ)
          ((app₁ 'vector-set!) (list {set V} Idx {set (-● ∅)}) ℓ Φ^ Ξ₀ Σ))]
      [(Vect αs)
       (define Vₐ (for/union : V^ ([α (in-list αs)])
                    (begin0 (Σᵥ@ Σ α)
                      (⊔ᵥ! Σ α (-● ∅)))))
       {set (ret! (T->R Vₐ Φ^) Ξ₀ Σ)}]
      [(Vect^ α _)
       {set (begin0 (ret! (T->R (Σᵥ@ Σ α) Φ^) Ξ₀ Σ)
              (⊔ᵥ! Σ α (-● ∅)))}]
      ;; Hash
      [(or (? Hash^?) (X/G _ (? Hash/C?) _))
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(hash-ref))))
       ((app₁ 'hash-ref) (list {set V} {set (-● ∅)}) ℓ Φ^ Ξ₀ Σ)]
      ;; Set
      [(or (? Set^?) (X/G _ (? Set/C?) _))
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(set-ref))))
       ((app₁ 'set-first) (list {set V}) ℓ Φ^ Ξ₀ Σ)]
      ;; Apply contract to unknowns
      [(? C?) #|TODO|# ∅]
      [_ ∅]))

  (: tag->leak : HV-Tag → α)
  (define (tag->leak tag)
    (match-define (mk-HV-Tag ?l H) tag)
    (mk-α (-α:hv (and ?l tag))))

  ;; For caching
  (splicing-local
      ((define cache : (Mutable-HashTable V Σᵥ) (make-hash))
       (: same-store? : Σᵥ Σᵥ (℘ α) → Boolean)
       (define (same-store? Σ₀ Σᵢ root)
         (define-set seen : α #:eq? #t #:as-mutable-hash? #t)
         (let go ([αs : (℘ α) root])
           (for/and : Boolean ([α : α (in-set αs)])
             (or (seen-has? α)
                 (let ([V₀ (Σᵥ@ Σ₀ α)]
                       [Vᵢ (Σᵥ@ Σᵢ α)])
                   (seen-add! α)
                   (and ((mutable? α) . implies . (equal? V₀ Vᵢ))
                        (set-andmap (compose go V-root) Vᵢ))))))))
    (define (seen? [V : V] [Σ : Σᵥ])
      (match (hash-ref cache V #f)
        [(? values Σ₀) (same-store? Σ₀ Σ (V-root V))]
        [#f #f]))
    (define (remember! [V : V] [Σ : Σᵥ]) (hash-set! cache V Σ))
    )

  #|
  (splicing-local
  (#;(define cache : (HashTable -V (Pairof -σ -δσ)) (make-hash))

       #;(: same-store? : (Pairof -σ -δσ) (Pairof -σ -δσ) (℘ ⟪α⟫) → Boolean)
       #;(define (same-store? memo₀ memo root)
         (match-define (cons σ₀ δσ₀) memo₀)
         (match-define (cons σ  δσ ) memo )
         (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
         (let loop ([αs : (℘ ⟪α⟫) root])
           (for/and : Boolean ([α : ⟪α⟫ (in-set αs)])
             (cond
               [(seen-has? α) #t]
               [else
                (seen-add! α)
                (define V₀ (σ@ σ₀ δσ₀ α mk-∅))
                (define V₁ (σ@ σ  δσ  α mk-∅))
                (and ((mutable? α) . implies . (equal? V₀ V₁))
                     (for/and : Boolean ([V (in-set V₁)])
                       (loop (V->⟪α⟫s V))))]))))

       #;(: seen? : -V -Σ -φ → Boolean)
       #;(define (seen? V Σ φ)
         (cond [(hash-ref cache V #f) =>
                (λ ([memo₀ : (Pairof -σ -δσ)])
                  (same-store? memo₀ (cons (-Σ-σ Σ) (-φ-cache φ)) (V->⟪α⟫s V)))]
               [else #f]))
       #;(: update-cache! : -V -Σ -φ → Void)
       #;(define (update-cache! V Σ φ) (hash-set! cache V (cons (-Σ-σ Σ) (-φ-cache φ))))
       ))
  ))
  |#
  )


