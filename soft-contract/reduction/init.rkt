#lang typed/racket/base

(provide 𝑰)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         (only-in "../proof-relation/base-assumptions.rkt" V-arity)
         "compile/utils.rkt"
         "compile/app.rkt"
         "havoc.rkt")

(: 𝑰 : (Listof -module) → (Values -σ -e))
;; Load the initial store and havoc-ing expression for given module list
(define (𝑰 ms)
  (define e† (gen-havoc-exp ms))
  (define hv (gen-havoc-clo ms))
  (define σ (⊥σ))
  (σ⊕*! σ [(-α->-⟪α⟫ (-α.def havoc-𝒾)) ↦ hv]
          [(-α->-⟪α⟫ (-α.wrp havoc-𝒾)) ↦ hv])
  ;(ensure-singletons σ) ; disable this in production
  (values σ e†))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Havoc
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 𝒙 (+x!/memo 'hv))
(define 𝐱 (-x 𝒙))
(define 𝐱s (list 𝐱))
(define ⟦rev-hv⟧ : -⟦e⟧!
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (let ([Vs (σ@ (-Σ-σ Σ) (-α->-⟪α⟫ (-α.def havoc-𝒾)))])
      (assert (= 1 (set-count Vs)))
      (⟦k⟧ (-W (list (set-first Vs)) havoc-𝒾) $ Γ ⟪ℋ⟫ Σ))))

(: gen-havoc-clo : (Listof -module) → -Clo)
(define (gen-havoc-clo ms)
  (define accs (prog-accs ms))

  (define ⟦e⟧ₕᵥ : -⟦e⟧!
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match-define (-Σ σ _ _) Σ)
      (define Vs (σ@ σ (ρ@ ρ 𝒙)))
      (define Wₕᵥ (-W¹ cloₕᵥ havoc-𝒾))

      #;(when (and (>= (set-count Vs) 4)
                 (for/or : Boolean ([V Vs]) (-Ar? V)))
        (printf "About to havoc ~a values at ~a:~n" (set-count Vs) (ρ@ ρ 𝒙))
        (for ([V Vs])
          (printf " - ~a~n" (show-V V)))
        #;(define κs (σₖ@ (-Σ-σₖ Σ) (⟦k⟧->αₖ ⟦k⟧)))
        #;(printf "before returning to: (~a) ~n" (set-count κs))
        #;(for ([κ κs])
          (printf " - ~a @ ~a~n"
                  (show-αₖ (⟦k⟧->αₖ (-κ-cont κ)))
                  (show-κ κ)))
        (printf "~n")
        #;(error "DONE"))
      

      #;(define (done-with-●)
        (⟦k⟧ (-W -●/Vs (-x (+x!/memo 'hv-rt 'done))) $ Γ ⟪ℋ⟫ Σ))

      (for*/union : (℘ -ς) ([V (in-set Vs)])
        ;(printf "havoc-ing ~a~n" (show-V V))
        (define W (-W¹ V 𝐱))
        (match V
          ;; Ignore first-order and opaque value
          [(or (-● _) (? -prim?))
           ∅ #;(done-with-●)]

          ;; Apply function with appropriate number of arguments
          [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
           
           (define tag (fun->tag V))

           (define (hv/arity [k : Natural]) : (℘ -ς)
             (define ●s : (Listof -W¹)
               (for/list ([i k])
                 (-W¹ -●/V (-x (+x!/memo 'hv #;k i)))))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'opq-ap k tag)) W ●s Γ ⟪ℋ⟫ Σ
                  (ap∷ (list Wₕᵥ) '() ⊥ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-res tag))
                       (hv∷ W (-ℒ ∅ (+ℓ/memo! 'hv-ap 'fun tag)) ⟦k⟧))))
           
           (define a (V-arity V))
           (match a
             [(arity-at-least k)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x!/memo 'hv-rt #;a))) $ Γ ⟪ℋ⟫ Σ)
                 (hv/arity (+ 1 k)))]
             [(? integer? k)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x!/memo 'hv-rt #;a))) $ Γ ⟪ℋ⟫ Σ)
                 (hv/arity k))]
             [(? list? ks)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x!/memo 'hv-rt #;a))) $ Γ ⟪ℋ⟫ Σ)
                 (for/union : (℘ -ς) ([k ks])
                   (cond [(integer? k) (hv/arity k)]
                         [else (error 'havoc "TODO: ~a" k)])))]
             [_
              ∅ #;(done-with-●)])]

          ;; If it's a struct, havoc all publically accessible fields
          [(or (-St s _) (-St* s _ _ _)) #:when s
           (∪ #;(done-with-●)
              (for/union : (℘ -ς) ([acc (hash-ref accs s →∅)])
               (define Acc (-W¹ acc acc))
               (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'ac-ap acc)) Acc (list W) Γ ⟪ℋ⟫ Σ
                    (ap∷ (list Wₕᵥ) '() ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-ap acc 'ac))
                         (hv∷ W (-ℒ ∅ (+ℓ/memo! 'hv-ap acc 'st)) ⟦k⟧)))))]

          ;; Havoc vector's content before erasing the vector with unknowns
          ;; Approximate vectors are already erased
          [(-Vector/hetero _ _) ∅ #;(done-with-●)]
          [(-Vector/homo   _ _) ∅ #;(done-with-●)]
          [(-Vector αs)
           (for/union : (℘ -ς) ([(α i) (in-indexed αs)])
             (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'vref i)) -vector-ref/W (list W Wᵢ) Γ ⟪ℋ⟫ Σ
                  (ap∷ (list Wₕᵥ) '() ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-ap 'ref i 0))
                       (hv∷ W (-ℒ ∅ (+ℓ/memo! 'hv-ap 'vect)) ⟦k⟧))))]
          [(-Vector^ α _)
           (for/union : (℘ -ς) ([V (σ@ σ α)])
             (define Wᵥ (-W¹ V #|TODO|# #f))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'vref #f)) Wₕᵥ (list Wᵥ) Γ ⟪ℋ⟫ Σ
                  (hv∷ W (-ℒ ∅ (+ℓ/memo! 'hv-ap 'vect)) ⟦k⟧)))]

          ;; Apply contract to unknown values
          [(? -C?)
           (log-warning "TODO: havoc contract combinators")
           ∅ #;(done-with-●)]))))
  
  (define cloₕᵥ : -Clo (-Clo (list 𝒙) ⟦e⟧ₕᵥ ⊥ρ ⊤Γ))
  cloₕᵥ)

(: gen-havoc-exp : (Listof -module) → -e)
;; Generate top-level expression havoc-ing modules' exports
(define (gen-havoc-exp ms)
  (define-set refs : -𝒾 #:as-mutable-hash? #t)
  
  (for ([m (in-list ms)])
    (match-define (-module path forms) m)
    (for* ([form forms] #:when (-provide? form)
           [spec (-provide-specs form)])
      (match-define (-p/c-item x _ _) spec)
      (refs-add! (-𝒾 x path))))

  (with-debugging/off
    ((ans) (-amb/simp #;(inst -begin/simp -e)
            (for/list ([ref (in-hash-keys refs)])
              (-@ havoc-𝒾 (list ref) (+ℓ!)))))
    (printf "gen-havoc-expr: ~a~n" (show-e ans))))

(: prog-accs : (Listof -module) → (HashTable -𝒾 (℘ -st-ac)))
;; Retrieve set of all public accessors from program, grouped by struct
(define (prog-accs ms)
  
  ;; Collect all defined accessors (`defs`) and exported identifiers (`decs`)
  (define defs : (HashTable Symbol -st-ac) (make-hasheq))
  (define decs : (HashTable Symbol #t    ) (make-hasheq))
  (for* ([m ms]
         [form (-module-body m)])
    (match form
      [(-provide specs)
       (for-each
        (match-lambda [(-p/c-item x _ _) (hash-set! decs x #t)])
        specs)]
      [(-define-values (list x) (? -st-ac? e))
       (hash-set! defs x e)]
      [_ (void)]))
  
  ;; Return exported accessors
  (for/fold ([m : (HashTable -𝒾 (℘ -st-ac)) (hash -𝒾-cons {set -car -cdr})])
            ([(x ac) (in-hash defs)] #:when (hash-has-key? decs x))
    (match-define (-st-ac s _) ac)
    (hash-update m s (λ ([acs : (℘ -st-ac)]) (set-add acs ac)) →∅)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Unimportant helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Hacky frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (hv∷ [W : -W¹] [ℒ : -ℒ] [⟦k⟧! : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧! _ $ Γ ⟪ℋ⟫ Σ) #:roots (W)
    (define Wₕᵥ (-W¹ (σ@¹ (-Σ-σ Σ) (-α->-⟪α⟫ (-α.def havoc-𝒾))) havoc-𝒾))
    (app havoc-path $ ℒ Wₕᵥ (list W) Γ ⟪ℋ⟫ Σ ⟦k⟧!)))

