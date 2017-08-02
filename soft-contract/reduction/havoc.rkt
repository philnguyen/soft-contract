#lang typed/racket/base

(provide havoc@)

(require racket/match
         racket/set
         racket/splicing
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit havoc@
  (import widening^ kont^ app^ proof-system^ local-prover^ for-gc^ sto^ pc^ val^ pretty-print^)
  (export havoc^)

  (splicing-local
      ((define cache : (HashTable -V (HashTable ⟪α⟫ (℘ -V))) (make-hash))
       
       (define (seen? [V : -V] [Σ : -Σ]) : Boolean
         (cond [(hash-ref cache V #f) =>
                (λ ([mσ₀ : (HashTable ⟪α⟫ (℘ -V))])
                  (define mσ (-Σ-σ Σ))
                  (map-equal?/spanning-root mσ₀ mσ (V->⟪α⟫s V) V->⟪α⟫s))]
               [else #f]))

       (define (update-cache! [V : -V] [Σ : -Σ]) : Void
         (hash-set! cache V (-Σ-σ Σ)))
       )

    (define (havoc [$ : -$] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧₀ : -⟦k⟧]) : (℘ -ς)
      #;(let ([Vs (σ@ Σ ⟪α⟫ₕᵥ)])
        (printf "~a havoc values:~n" (set-count Vs))
        (for ([V (in-set Vs)])
          (printf "  - ~a~n" (show-V V))))
      (for/fold ([res : (℘ -ς) (⟦k⟧₀ -Void.W∅ $ ⊤Γ ⟪ℋ⟫ Σ)])
                ([V (in-set (σ@ Σ ⟪α⟫ₕᵥ))] #:unless (seen? V Σ))
        (update-cache! V Σ)
        (∪ res (havoc-V V $ ⟪ℋ⟫ Σ (hv∷ ⟦k⟧₀))))))

  (define (havoc-V [V : -V] [$ : -$] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (define (done) ∅ #;(⟦k⟧ -Void/W∅ ⊤Γ ⟪ℋ⟫ Σ))

    (define W (-W¹ V (loc->ℓ (loc 'hv.var 0 0 '()))))
    (match V
      ;; Ignore first-order and opaque value
      [(or (-● _) (? -prim?)) (done)]

      ;; Apply function with appropriate number of arguments
      [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
       
       (define (do-hv [k : (U Natural arity-at-least)]) : (℘ -ς)
         (match k
           [(? exact-nonnegative-integer? k)
            (define args : (Listof -W¹)
              (for/list ([i k])
                (-W¹ (+●) (+ℓ/memo k i))))
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'opq-ap k))))
            (app ℓ W args $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [(arity-at-least n)
            (define args₀ : (Listof -W¹)
              (for/list ([i n])
                (-W¹ (+●) (+ℓ/memo n i))))
            (define argᵣ (-W¹ (+● 'list?) (+ℓ/memo n n)))
            (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'opq-app n 'vararg))))
            (app ℓ (+W¹ 'apply) `(,W ,@args₀ ,argᵣ) $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)]))
       
       (match (V-arity V)
         [(? list? ks)
          (for/union : (℘ -ς) ([k ks])
                     (cond [(integer? k) (do-hv k)]
                           [else (error 'havoc "TODO: ~a" k)]))]
         [(and k (or (? index?) (? arity-at-least?))) (do-hv k)])]

      ;; If it's a struct, havoc and widen each public field
      [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _))
       #:when 𝒾
       (∪
        (for/union : (℘ -ς) ([acc (get-public-accs 𝒾)])
                   (define Acc (-W¹ acc acc))
                   (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'ac (-𝒾-name 𝒾)))))
                   (app ℓ Acc (list W) $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧))
        (for/union : (℘ -ς) ([mut (get-public-muts 𝒾)])
                   (define Mut (-W¹ mut mut))
                   (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'mut (-𝒾-name 𝒾)))))
                   (app ℓ Mut (list W (-W¹ (+●) #f)) $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)))]

      ;; Havoc vector's content before erasing the vector with unknowns
      ;; Guarded vectors are already erased
      [(? -Vector/guard?)
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(vector/guard))))
       (define Wᵢ (-W¹ (+● 'exact-nonnegative-integer?) #f))
       (∪
        (app (ℓ-with-id ℓ 'ref) (+W¹ 'vector-ref) (list W Wᵢ) $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (app (ℓ-with-id ℓ 'mut) (+W¹ 'vector-set!) (list W Wᵢ (-W¹ (+●) #f)) $ ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [(-Vector αs)
       ;; Widen each field first. No need to go through `vector-set!` b/c there's no
       ;; contract protecting it
       (for ([α (in-list αs)])
         (σ⊕V! Σ α (+●)))
       ;; Access vector at opaque field
       (for*/union : (℘ -ς) ([α : ⟪α⟫ αs] [V (in-set (σ@ Σ α))])
                   (⟦k⟧ (-W (list V) #f) $ ⊤Γ ⟪ℋ⟫ Σ))]
      
      [(-Vector^ α _)
       (σ⊕V! Σ α (+●))
       (for/union : (℘ -ς) ([V (in-set (σ@ Σ α))])
                  (⟦k⟧ (-W (list V) #f) $ ⊤Γ ⟪ℋ⟫ Σ))]

      ;; Apply contract to unknown values
      [(? -C?)
       (log-warning "TODO: havoc contract combinators")
       (done)]))

  (define -Void.W∅ (+W (list -void) #f))

  (define (gen-havoc-expr [ms : (Listof -module)]) : -e
    (define refs
      ;; collect as list to enforce some order to reduce confusion when debugging
      (for*/list : (Listof -𝒾) ([m (in-list ms)]
                                [path (in-value (-module-path m))]
                                [form (in-list (-module-body m))] #:when (-provide? form)
                                [spec (in-list (-provide-specs form))] #:when (-p/c-item? spec))
        (match-define (-p/c-item x _ _) spec)
        (-𝒾 x path)))

    (with-debugging/off
      ((ans) (-@ (-•) refs +ℓ₀))
      (printf "gen-havoc-expr: ~a~n" (show-e ans))))

  (: +ℓ/memo : Natural Natural → ℓ)
  (define (+ℓ/memo arity ith) (loc->ℓ (loc 'havoc-opq arity ith '()))))


