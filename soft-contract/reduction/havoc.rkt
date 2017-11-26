#lang typed/racket/base

(provide havoc@)

(require racket/match
         racket/set
         racket/list
         racket/sequence
         racket/splicing
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit havoc@
  (import static-info^ widening^ kont^ app^ proof-system^ instr^
          for-gc^ sto^ path^ val^ pretty-print^)
  (export havoc^)

  (splicing-local
      ((define cache : (HashTable -V (HashTable ⟪α⟫ (℘ -V))) (make-hash))

       (: seen? : -V -Σ → Boolean)
       (define (seen? V Σ)
         (cond [(hash-ref cache V #f) =>
                (λ ([mσ₀ : (HashTable ⟪α⟫ (℘ -V))])
                  (define mσ (-Σ-σ Σ))
                  (map-equal?/spanning-root mσ₀ mσ (V->⟪α⟫s V) V->⟪α⟫s mutable?))]
               [else #f]))
       (: update-cache! : -V -Σ → Void)
       (define (update-cache! V Σ) (hash-set! cache V (-Σ-σ Σ)))
       )

    (: havoc : HV-Tag -φ -Σ -⟦k⟧ → (℘ -ς))
    (define (havoc tag φ Σ ⟦k⟧)
      (for/fold ([res : (℘ -ς) (⟦k⟧ (list {set -void}) H∅ φ Σ)])
                ([V (in-set (σ@ Σ (-φ-cache φ) (-α->⟪α⟫ (-α.hv tag))))] #:unless (seen? V Σ))
        (update-cache! V Σ)
        (∪ res (havoc-V V φ Σ (hv∷ tag ⟦k⟧))))))

  (: havoc-V : -V -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (havoc-V V φ Σ ⟦k⟧)
    (define (done) ∅ #;(⟦k⟧ -Void/W∅ ⊤Γ H Σ))

    (match V
      ;; Ignore first-order and opaque value
      [(or (-● _) (? -prim?)) (done)]

      ;; Apply function with appropriate number of arguments
      [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))

       (: do-hv : (U Natural arity-at-least) → (℘ -ς))
       (define do-hv
         (match-lambda
           [(? exact-nonnegative-integer? k)
            (define args #|TODO|# (make-list k {set (-● ∅)}))
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'opq-ap k))))
            (app₁ ℓ V args H∅ φ Σ ⟦k⟧)]
           [(arity-at-least n)
            (define args-init #|TODO|# (make-list n {set (-● ∅)}))
            (define args-rest #|TODO|# {set (-● ∅)})
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

  (: gen-havoc-expr : (Listof -module) → -e)
  (define (gen-havoc-expr ms)
    (define refs
      (for*/list : (Listof -x) ([m (in-list ms)]
                                [path (in-value (-module-path m))]
                                [form (in-list (-module-body m))] #:when (-provide? form)
                                [spec (in-list (-provide-specs form))] #:when (-p/c-item? spec))
        (match-define (-p/c-item x _ _) spec)
        (-x (-𝒾 x path) (loc->ℓ (loc 'top-level-havoc 0 0 (list x))))))
    (define ℓ (loc->ℓ (loc 'havoc-expr 0 0 '())))
    (with-debugging/off
      ((ans) (-@ (-•) refs ℓ))
      (printf "gen-havoc-expr: ~a~n" (show-e ans))))

  (: add-leak! : HV-Tag -Σ -φ (U -V^ (Listof -V^)) → -φ)
  (define (add-leak! tag Σ φ V)
    (define α (-α->⟪α⟫ (-α.hv tag)))
    (define (keep-behavioral [V : -V^]) : -V^
      (for/fold ([V : -V^ V])
                ([Vᵢ (in-set V)] #:unless (behavioral? (-Σ-σ Σ) (-φ-cache φ) Vᵢ))
        (set-remove V Vᵢ)))
    (define V^
      (cond
        [(set? V) (keep-behavioral V)]
        [else
         (for/fold ([V^ : -V^ ∅]) ([Vᵢ (in-list V)])
           (V⊕ V^ (keep-behavioral Vᵢ)))]))
    (mut! Σ φ α V^))
  )


