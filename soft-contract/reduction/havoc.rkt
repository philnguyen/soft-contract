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
         "signatures.rkt"
         )

(define-unit havoc@
  (import val^ sto^ evl^)
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
  
  (: add-leak! : ((U HV-Tag α) Σ (U V^ W) → Void))
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
    (define-values (W^ Φ^) (collapse-R^ R^))
    (define α• (tag->leak tag))
    (for ([W (in-set W^)])
      (add-leak! α• Σ W))
    (for/union : (℘ Ξ) ([V (in-set (Σᵥ@ Σ α•))])
       (havoc-V V Φ^ Ξ₀ Σ)))

  (: havoc-V : V Φ^ Ξ:co Σ → (℘ Ξ))
  (define (havoc-V V Φ^ Ξ Σ) ???)

  (: tag->leak : HV-Tag → α)
  (define (tag->leak tag)
    (match-define (cons ?l H) tag)
    (mk-α (-α:hv (and ?l tag))))

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
       )

    (: havoc : HV-Tag Φ^ Ξ:co Σ → (℘ Ξ))
    (define (havoc tag Φ^ Ξ Σ)
      ???
      #;(for/fold ([res : (℘ -ς) (⟦k⟧ (list {set -void}) H∅ φ Σ)])
                ([V (in-set (σ@ Σ (-φ-cache φ) (-α->⟪α⟫ (-α.hv tag)) mk-∅))]
                 #:unless (seen? V Σ φ))
        (update-cache! V Σ φ)
        (∪ res (havoc-V V φ Σ (hv∷ tag ⟦k⟧))))))

  (: havoc-V : V Φ^ Ξ:co Σ → (℘ Ξ))
  (define (havoc-V V Φ^ Ξ Σ)
    (define (done) ∅ #;(⟦k⟧ -Void/W∅ ⊤Γ H Σ))
    ???
    #;(match V
      ;; Ignore first-order and opaque value
      [(or (? integer?) (-● _) (? -prim?)) (done)]

      ;; Apply function with appropriate number of arguments
      [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))

       (: do-hv : (U Natural arity-at-least) → Ξ)
       (define do-hv
         (match-lambda
           [(? exact-nonnegative-integer? k)
            (define args (build-list k (λ _ {set (fresh-sym!)})))
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'opq-ap k))))
            (app₁ ℓ V args H∅ φ Σ ⟦k⟧)]
           [(arity-at-least n)
            (define args-init (build-list n (λ _ {set (fresh-sym!)})))
            (define args-rest {set (fresh-sym!)})
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'opq-app n 'vararg))))
            (app₁ ℓ 'apply (append args-init (list args-rest)) H∅ φ Σ ⟦k⟧)]))
       
       (match (V-arity V)
         [(? list? ks)
          (for/union : (℘ -ς) ([k (in-list ks)])
            (cond [(integer? k) (do-hv k)]
                  [else (error 'havoc "TODO: ~a" k)]))]
         [(and k (or (? index?) (? arity-at-least?))) (do-hv k)])]

      ;; If it's a struct, havoc and widen each public field
      [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _))
       #:when 𝒾
       (∪ (for/union : (℘ -ς) ([acc (get-public-accs 𝒾)])
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'ac (-𝒾-name 𝒾)))))
            (app₁ ℓ acc (list {set V}) H∅ φ Σ ⟦k⟧))
          (for/union : (℘ -ς) ([mut (get-public-muts 𝒾)])
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'mut (-𝒾-name 𝒾)))))
            (app₁ ℓ mut (list {set V} {set (-● {set 'exact-nonnegative-integer?})}) H∅ φ Σ ⟦k⟧)))]

      ;; Havoc vector's content before erasing the vector with unknowns
      ;; Guarded vectors are already erased
      [(? -Vector/guard?)
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(vector/guard))))
       (define Vᵢ^ {set (-● {set 'exact-nonnegative-integer?})})
       (∪ (app₁ (ℓ-with-id ℓ 'ref) 'vector-ref (list {set V} Vᵢ^) H∅ φ Σ ⟦k⟧)
          (app₁ (ℓ-with-id ℓ 'mut) 'vector-set! (list {set V} Vᵢ^ {set (-● ∅)}) H∅ φ Σ ⟦k⟧))]
      [(-Vector αs)
       ;; Widen each field first. No need to go through `vector-set!` b/c there's no
       ;; contract protecting it
       (define φ*
         (for/fold ([φ : -φ φ]) ([α (in-list αs)])
           (mut! Σ φ α {set (-● ∅)})))
       ;; Access vector at opaque field
       (define V^ (for/union : -V^ ([α (in-list αs)]) (σ@ Σ (-φ-cache φ) α)))
       (⟦k⟧ (list V^) H∅ φ* Σ)]
      
      [(-Vector^ α _)
       (⟦k⟧ (list (σ@ Σ (-φ-cache φ) α)) H∅ (mut! Σ φ α {set (-● ∅)}) Σ)]

      [(or (? -Hash/guard?) (? -Hash^?))
       (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'hash-ref))))
       (app₁ ℓ 'hash-ref (list {set V} {set (-● ∅)}) H∅ φ Σ ⟦k⟧)]
      [(or (? -Set/guard?) (? -Set^?))
       (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'set-ref))))
       (app₁ ℓ 'set-first (list {set V}) H∅ φ Σ ⟦k⟧)]

      ;; Apply contract to unknown values
      [(? -C?)
       (log-warning "TODO: havoc contract combinators")
       (done)]))
  |#
  )


