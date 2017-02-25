#lang typed/racket/base

(provide havoc gen-havoc-expr)

(require racket/match
         racket/set
         racket/splicing
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         "../externals/def-ext.rkt"
         "../externals/def-ext-runtime.rkt"
         (only-in "../proof-relation/base-assumptions.rkt" V-arity)
         "compile/utils.rkt"
         "compile/app.rkt"
         )

(splicing-local
    ((define cache : (HashTable -V (HashTable ⟪α⟫ (℘ -V))) (make-hash))
     
     (: seen? : -V -Σ → Boolean)
     (define (seen? V Σ)
       (cond [(hash-ref cache V #f) =>
              (λ ([mσ₀ : (HashTable ⟪α⟫ (℘ -V))])
                (define mσ (-σ-m (-Σ-σ Σ)))
                (map-equal?/spanning-root mσ₀ mσ (V->⟪α⟫s V) V->⟪α⟫s))]
             [else #f]))

     (: update-cache! : -V -Σ → Void)
     (define (update-cache! V Σ)
       (hash-set! cache V (-σ-m (-Σ-σ Σ))))
     )

  (: havoc : -⟪ℋ⟫ -Σ → (℘ -ς))
  (define (havoc ⟪ℋ⟫ Σ)
    #;(let ([Vs (σ@ Σ ⟪α⟫ₕᵥ)])
      (printf "~a havoc values:~n" (set-count Vs))
      (for ([V (in-set Vs)])
        (printf "  - ~a~n" (show-V V))))
    (define ⟦k⟧₀ (rt (-ℋ𝒱)))
    (for/fold ([res : (℘ -ς) (⟦k⟧₀ -Void/W∅ $∅ ⊤Γ ⟪ℋ⟫ Σ)])
              ([V (in-set (σ@ Σ ⟪α⟫ₕᵥ))] #:unless (seen? V Σ))
      (update-cache! V Σ)
      (∪ res (havoc-V V ⟪ℋ⟫ Σ (hv∷ ⟦k⟧₀))))))



(define/memoeq (hv∷ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W Vs _) A)
    (for ([V (in-list Vs)])
      (add-leak! Σ V))
    {set (-ς↑ (-ℋ𝒱) ⊤Γ ⟪ℋ⟫)}))

(splicing-local
    ((define 𝒙 (+x!/memo 'hv))
     (define 𝐱 (-x 𝒙))
     
     #;(: fun->tag : -V → Any)
     ;; Return tag distinguishing function objects
     #;(define fun->tag
       (match-lambda
         [(-Clo xs ⟦e⟧ _ _) (cons xs ⟦e⟧)]
         [(-Case-Clo clauses _ _) clauses]
         [(-Ar grd _ _)
          (match grd
            [(-=> doms _ _) (length doms)]
            [(-=>i _ (list (-Clo xs ⟦d⟧ _ _) _ _) _) (cons xs ⟦d⟧)]
            [(-Case-> sigs _)
             (for/list : (Listof Natural) ([sig sigs])
               (length (car sig)))])]
         [_ #f])))
  
  (: havoc-V : -V -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (havoc-V V ⟪ℋ⟫ Σ ⟦k⟧)
    
    (define (done) (⟦k⟧ -Void/W∅ $∅ ⊤Γ ⟪ℋ⟫ Σ))

    ;(printf "havoc-ing ~a~n" (show-V V))
    (define W (-W¹ V 𝐱))
    (match V
      ;; Ignore first-order and opaque value
      [(or (-● _) (? -prim?)) (done)]

      ;; Apply function with appropriate number of arguments
      [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
       
       (define (do-hv [k : Natural]) : (℘ -ς)
         (define args : (Listof -W¹)
           (for/list ([i k])
             (-W¹ -●/V (-x (+x!/memo 'arg i)))))
         (define ℓ (loc->ℓ (loc 'havoc 0 0 (list k 'opq-ap))))
         #;(begin
           (printf "app: ~a~n" (show-W¹ W))
           (for ([W (in-list args)])
             (printf "  - ~a~n" (show-W¹ W)))
           (printf "~n"))
         (app 'havoc $∅ (-ℒ ∅ ℓ) W args ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧))
       
       (match (V-arity V)
         [(arity-at-least k) (do-hv (+ 1 k))]
         [(? integer? k) (do-hv k)]
         [(? list? ks)
          (for/union : (℘ -ς) ([k ks])
            (cond [(integer? k) (do-hv k)]
                  [else (error 'havoc "TODO: ~a" k)]))]
         [_ (done)])]

      ;; If it's a struct, havoc and widen each public field
      [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _)) #:when 𝒾
       (∪
        (for/union : (℘ -ς) ([acc (get-public-accs 𝒾)])
          (define Acc (-W¹ acc acc))
          (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'hv-ac (show-o acc)))))
          (app 'havoc $∅ (-ℒ ∅ ℓ) Acc (list W) ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧))
        (for/union : (℘ -ς) ([mut (get-public-muts 𝒾)])
          (define Mut (-W¹ mut mut))
          (define ℓ (loc->ℓ (loc 'havoc 0 0 (list 'hv-mut (show-o mut)))))
          (app 'havoc $∅ (-ℒ ∅ ℓ) Mut (list W -●/W¹∅) ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)))]

      ;; Havoc vector's content before erasing the vector with unknowns
      ;; Guarded vectors are already erased
      [(? -Vector/guard?)
       (define ℓ (loc->ℓ (loc 'havoc 0 0 '(vector/guard))))
       (define Wᵢ (-W¹ -Nat/V #f))
       (∪
        (app 'havoc $∅ (-ℒ ∅ (ℓ-with-id ℓ 'ref)) -vector-ref/W (list W Wᵢ) ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧)
        (app 'havoc $∅ (-ℒ ∅ (ℓ-with-id ℓ 'mut)) -vector-set!/W (list W Wᵢ -●/W¹∅) ⊤Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [(-Vector αs)
       ;; Widen each field first. No need to go through `vector-set!` b/c there's no
       ;; contract protecting it
       (for ([α (in-list αs)])
         (σ⊕! Σ α -●/V))
       ;; Access vector at opaque field
       (for*/union : (℘ -ς) ([α : ⟪α⟫ αs] [V (in-set (σ@ Σ α))])
          (⟦k⟧ (-W (list V) #f) $∅ ⊤Γ ⟪ℋ⟫ Σ))]
      
      [(-Vector^ α _)
       (σ⊕! Σ α -●/V)
       (for/union : (℘ -ς) ([V (in-set (σ@ Σ α))])
         (⟦k⟧ (-W (list V) #f) $∅ ⊤Γ ⟪ℋ⟫ Σ))]

      ;; Apply contract to unknown values
      [(? -C?)
       (log-warning "TODO: havoc contract combinators")
       (done)])))

(define -Void/W∅ (-W -Void/Vs #f))

(: gen-havoc-expr : (Listof -module) → -e)
(define (gen-havoc-expr ms)
  (define refs : (Listof -𝒾)
    ;; collect as list to enforce some order to reduce confusion when debugging
    (for*/list ([m (in-list ms)]
                [path (in-value (-module-path m))]
                [form (in-list (-module-body m))] #:when (-provide? form)
                [spec (in-list (-provide-specs form))])
      (match-define (-p/c-item x _ _) spec)
      (-𝒾 x path)))

  (with-debugging/off
    ((ans) (-@ (-•) refs +ℓ₀))
    (printf "gen-havoc-expr: ~a~n" (show-e ans))))
