#lang typed/racket/base

(provide havoc* havoc
         havoc*∷ havoc∷ hv∷
         gen-havoc-expr)

(require racket/match
         racket/set
         racket/splicing
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         (only-in "../proof-relation/base-assumptions.rkt" V-arity)
         "compile/utils.rkt"
         "compile/app.rkt"
         )

(: havoc* : -ℒ (℘ -V) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (havoc* ℒ Vs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ σₖ _) Σ)
  (define ⟦k⟧* (havoc*∷ ℒ Vs ⟦k⟧))
  (for/fold ([ac : (℘ -ς) (⟦k⟧ -Void/W∅ $∅ Γ ⟪ℋ⟫ Σ)])
            ([V (in-set Vs)])
    (define αₖ (-ℋ𝒱 ℒ V))
    (define κ (-κ ⟦k⟧* Γ ⟪ℋ⟫ 'void '()))
    (σₖ⊔! σₖ αₖ κ)
    (set-add ac (-ς↑ αₖ Γ ⟪ℋ⟫))))

(splicing-local
    ((define 𝒙 (+x!/memo 'hv))
     (define 𝐱 (-x 𝒙))
     
     (: fun->tag : -V → #|essentially Any, just do document "optional"|# (Option Any))
     ;; Return tag distinguishing function objects
     (define fun->tag
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
         [_ #f]))
     )
  (: havoc : -ℒ -V -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (havoc ℒ V Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-Σ σ _ _) Σ)
    
    (define (done) (⟦k⟧ -Void/W∅ $∅ Γ ⟪ℋ⟫ Σ))

    ;(printf "havoc-ing ~a~n" (show-V V))
    (define W (-W¹ V 𝐱))
    (match V
      ;; Ignore first-order and opaque value
      [(or (-● _) (? -prim?)) (done)]

      ;; Apply function with appropriate number of arguments
      [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
       
       (define tag (fun->tag V))

       (define (hv/arity [k : Natural]) : (℘ -ς)
         (define-values (xs ●s)
           (for/lists ([xs : (Listof Symbol)] [●s : (Listof -W¹)])
                      ([i k])
             (define x (+x!/memo 'hv #;k i))
             (values x (-W¹ -●/V (-x x)))))
         (define Γ*
           (for/fold ([Γ : -Γ Γ]) ([x (in-list xs)])
             (invalidate Γ x)))
         (app 'havoc $∅ (ℒ-with-mon ℒ (+ℓ/memo! 'opq-ap k tag)) W ●s Γ* ⟪ℋ⟫ Σ
              (hv∷ (ℒ-with-mon ℒ (+ℓ/memo! 'hv-res tag)) ⟦k⟧)))
       
       (define a (V-arity V))
       (match a
         [(arity-at-least k)
          (hv/arity (+ 1 k))]
         [(? integer? k)
          (hv/arity k)]
         [(? list? ks)
          (for/union : (℘ -ς) ([k ks])
            (cond [(integer? k) (hv/arity k)]
                  [else (error 'havoc "TODO: ~a" k)]))]
         [_ (done)])]

      ;; If it's a struct, havoc all publically accessible fields
      [(or (-St 𝒾 _) (-St* 𝒾 _ _ _)) #:when 𝒾
       (for/union : (℘ -ς) ([acc (get-public-accs 𝒾)])
         (define Acc (-W¹ acc acc))
         (app 'havoc $∅ (ℒ-with-mon ℒ (+ℓ/memo! 'ac-ap acc)) Acc (list W) Γ ⟪ℋ⟫ Σ
              (hv∷ (ℒ-with-mon ℒ (+ℓ/memo! 'hv-ap acc 'ac)) ⟦k⟧)))]

      ;; Havoc vector's content before erasing the vector with unknowns
      ;; Approximate vectors are already erased
      [(-Vector/hetero _ _) (done)]
      [(-Vector/homo   _ _) (done)]
      [(-Vector αs)
       (for/union : (℘ -ς) ([(α i) (in-indexed αs)])
         (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
         (app 'havoc $∅ (ℒ-with-mon ℒ (+ℓ/memo! 'vref i)) -vector-ref/W (list W Wᵢ) Γ ⟪ℋ⟫ Σ
              (hv∷ (ℒ-with-mon ℒ (+ℓ/memo! 'hv-ap 'ref i 0)) ⟦k⟧)))]
      [(-Vector^ α _)
       (for/set: : (℘ -ς) ([V (σ@ σ α)])
         (define αₖ (-ℋ𝒱 (ℒ-with-mon ℒ (+ℓ/memo! 'vref #f)) V))
         (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ 'void '()))
         (σₖ⊔! (-Σ-σₖ Σ) αₖ κ)
         (-ς↑ αₖ Γ ⟪ℋ⟫))]

      ;; Apply contract to unknown values
      [(? -C?)
       (log-warning "TODO: havoc contract combinators")
       (done)])))

(define -Void/W∅ (-W -Void/Vs #f))

(define/memo (havoc*∷ [ℒ : -ℒ] [Vs : (℘ -V)] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Vs)
    (havoc* ℒ Vs Γ ⟪ℋ⟫ Σ ⟦k⟧)))

(define/memo (havoc∷ [ℒ : -ℒ] [V : -V] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (V)
    (havoc ℒ V Γ ⟪ℋ⟫ Σ ⟦k⟧)))

(define/memo (hv∷ [ℒ : -ℒ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots ()
    (match-define (-W Vs _) A)
    (for/set: : (℘ -ς) ([V (in-list Vs)])
      (define αₖ (-ℋ𝒱 ℒ V))
      (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ 'void '()))
      (σₖ⊔! (-Σ-σₖ Σ) αₖ κ)
      (-ς↑ αₖ Γ ⟪ℋ⟫))))

(: gen-havoc-expr : (Listof -module) → -e)
(define (gen-havoc-expr ms)
  (define-set refs : -𝒾 #:as-mutable-hash? #t)
  
  (for ([m (in-list ms)])
    (match-define (-module path forms) m)
    (for* ([form (in-list forms)] #:when (-provide? form)
           [spec (in-list (-provide-specs form))])
      (match-define (-p/c-item x _ _) spec)
      (refs-add! (-𝒾 x path))))

  (with-debugging/off
    ((ans) (-amb/simp #;(inst -begin/simp -e)
                      (for/list ([ref (in-hash-keys refs)])
                        (-@ (•!) (list ref) (+ℓ!)))))
    (printf "gen-havoc-expr: ~a~n" (show-e ans))))
