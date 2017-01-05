#lang typed/racket/base

(provide havoc gen-havoc-clo gen-havoc-exp)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         (only-in "../proof-relation/base-assumptions.rkt" V-arity)
         "../externals/main.rkt" ; for side-effects
         "compile/utils.rkt"
         "compile/app.rkt")

(: havoc : -ℒ (℘ -V) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (havoc ℒ Vs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (define ⟦k⟧* #|FIXME|# (havoc∷ ℒ Vs ⟦k⟧))
  (define Wₕᵥ (-W¹ (σ@¹ σ (-α->-⟪α⟫ havoc-𝒾)) #f))
  (for/fold ([ac : (℘ -ς) (⟦k⟧ -Void/W∅ $∅ Γ ⟪ℋ⟫ Σ)])
            ([V (in-set Vs)])
    (∪ ac
       (app 'Λ $∅ ℒ Wₕᵥ (list (-W¹ V #f)) Γ ⟪ℋ⟫ Σ ⟦k⟧*))))

(define/memo (havoc∷ [ℒ : -ℒ] [Vs : (℘ -V)] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Vs)
    (havoc ℒ Vs Γ ⟪ℋ⟫ Σ ⟦k⟧)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 𝒙 (+x!/memo 'hv))
(define 𝐱 (-x 𝒙))

(: gen-havoc-clo : (Listof -module) → -Clo)
(define (gen-havoc-clo ms)
  (define accs (prog-accs ms))

  (define ⟦e⟧ₕᵥ : -⟦e⟧
    (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match-define (-Σ σ _ _) Σ)
      (define Vs (σ@ σ (ρ@ ρ 𝒙)))
      (define Wₕᵥ (-W¹ cloₕᵥ #f))
      
      (define (done) (⟦k⟧ -Void/W∅ $ Γ ⟪ℋ⟫ Σ))

      (for*/union : (℘ -ς) ([V (in-set Vs)])
        ;(printf "havoc-ing ~a~n" (show-V V))
        (define W (-W¹ V 𝐱))
        (match V
          ;; Ignore first-order and opaque value
          [(or (-● _) (? -prim?)) (done)]

          ;; Apply function with appropriate number of arguments
          [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
           
           (define tag (fun->tag V))

           (define (hv/arity [k : Natural]) : (℘ -ς)
             (define ●s : (Listof -W¹)
               (for/list ([i k])
                 (-W¹ -●/V (-x (+x!/memo 'hv #;k i)))))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'opq-ap k tag)) W ●s Γ ⟪ℋ⟫ Σ
                  (ap∷ (list Wₕᵥ) '() ⊥ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-res tag))
                       ⟦k⟧)))
           
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
          [(or (-St s _) (-St* s _ _ _)) #:when s
           (∪ (for/union : (℘ -ς) ([acc (hash-ref accs s →∅)])
               (define Acc (-W¹ acc acc))
               (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'ac-ap acc)) Acc (list W) Γ ⟪ℋ⟫ Σ
                    (ap∷ (list Wₕᵥ) '() ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-ap acc 'ac))
                         ⟦k⟧))))]

          ;; Havoc vector's content before erasing the vector with unknowns
          ;; Approximate vectors are already erased
          [(-Vector/hetero _ _) (done)]
          [(-Vector/homo   _ _) (done)]
          [(-Vector αs)
           (for/union : (℘ -ς) ([(α i) (in-indexed αs)])
             (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'vref i)) -vector-ref/W (list W Wᵢ) Γ ⟪ℋ⟫ Σ
                  (ap∷ (list Wₕᵥ) '() ρ havoc-path (-ℒ ∅ (+ℓ/memo! 'hv-ap 'ref i 0))
                       ⟦k⟧)))]
          [(-Vector^ α _)
           (for/union : (℘ -ς) ([V (σ@ σ α)])
             (define Wᵥ (-W¹ V #|TODO|# #f))
             (app havoc-path $ (-ℒ ∅ (+ℓ/memo! 'vref #f)) Wₕᵥ (list Wᵥ) Γ ⟪ℋ⟫ Σ
                  ⟦k⟧))]

          ;; Apply contract to unknown values
          [(? -C?)
           (log-warning "TODO: havoc contract combinators")
           (done)]))))
  
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

(define -Void/W∅ (-W -Void/Vs #f))
