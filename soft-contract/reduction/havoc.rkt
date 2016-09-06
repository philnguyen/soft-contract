#lang typed/racket/base

(provide gen-havoc-exp gen-havoc-clo)

(require "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         racket/set
         racket/match)

(define 𝒙 (+x!))
(define 𝐱 (-x 𝒙))
(define 𝐱s (list 𝐱))
(define ⟦rev-hv⟧ : -⟦e⟧!
  (λ (ρ Γ 𝒞 Σ ⟦k⟧)
    (let-values ([(Vs _) (σ@ (-Σ-σ Σ) (-α.def havoc-𝒾))])
      (assert (= 1 (set-count Vs)))
      (⟦k⟧ (-W (list (set-first Vs)) havoc-𝒾) Γ 𝒞 Σ))))

(: gen-havoc-clo : (Listof -module) → -Clo)
(define (gen-havoc-clo ms)
  (define accs (prog-accs ms))

  (define ⟦e⟧ : -⟦e⟧!
    (λ (ρ Γ 𝒞 Σ ⟦k⟧)
      (match-define (-Σ σ _ _) Σ)
      (for*/union : (℘ -ς) ([σr (in-value (hash-ref σ (ρ@ ρ 𝒙)))]
                           [V (in-set (-σr-vals σr))])
        (define W (-W¹ V 𝐱))
        (match V
          ;; Ignore first-order and opaque value
          [(or (-● _) (? -prim?)) ∅]

          ;; Apply function with appropriate number of arguments
          [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))

           (define (hv/arity [k : Natural]) : (℘ -ς)
             (error 'hv/arity "TODO"))
           
           (define a (V-arity V))
           (match a
             [(arity-at-least k)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x/memo! 'hv-rt a))) Γ 𝒞 Σ)
                 (hv/arity (+ 1 k)))]
             [(? integer? k)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x/memo! 'hv-rt a))) Γ 𝒞 Σ)
                 (hv/arity k))]
             [(? list? ks)
              (∪ (⟦k⟧ (-W -●/Vs (-x (+x/memo! 'hv-rt a))) Γ 𝒞 Σ)
                 (for/union : (℘ -ς) ([k ks])
                   (cond [(integer? k) (hv/arity k)]
                         [else (error 'havoc "TODO: ~a" k)])))]
             [_ ∅])]

          ;; If it's a struct, havoc all publically accessible fields
          [(or (-St s _) (-St* s _ _ _)) #:when s
           (error 'havoc "TODO: struct")]

          ;; Havoc vector's content before erasing the vector with unknowns
          ;; Approximate vectors are already erased
          [(-Vector/hetero _ _) ∅]
          [(-Vector/homo   _ _) ∅]
          [(-Vector αs)
           (error 'havoc "TODO: vector")]

          ;; Apply contract to unknown values
          [(? -C?)
           (log-warning "TODO: havoc contract combinators")
           ∅]))))
  
  (-Clo (list 𝒙) ⟦e⟧ ⊥ρ ⊤Γ))

(: gen-havoc-exp : (Listof -module) → -e)
;; Generate top-level expression havoc-ing modules' exports
(define (gen-havoc-exp ms)
  (define-set refs : -𝒾)
  
  (for ([m (in-list ms)])
    (match-define (-module path forms) m)
    (for* ([form forms] #:when (-provide? form)
           [spec (-provide-specs form)])
      (match-define (-p/c-item x _ _) spec)
      (refs-add! (-𝒾 x path))))
  
  (-amb/simp (for/list ([ref (in-set refs)])
               (-@ havoc-𝒾 (list ref) (+ℓ!)))))

(: prog-accs : (Listof -module) → (HashTable -struct-info (℘ -st-ac)))
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
  (for/fold ([m : (HashTable -struct-info (℘ -st-ac)) (hash -s-cons {set -car -cdr})])
            ([(x ac) (in-hash defs)] #:when (hash-has-key? decs x))
    (match-define (-st-ac s _) ac)
    (hash-update m s (λ ([acs : (℘ -st-ac)]) (set-add acs ac)) →∅)))
