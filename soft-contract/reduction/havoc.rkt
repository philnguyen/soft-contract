#lang typed/racket/base

(provide gen-havoc-Clo gen-havoc-exp havoc-𝒾)

(require racket/match
         racket/set
         (except-in racket/function arity-includes?)
         (except-in racket/list remove-duplicates)
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "step.rkt"
         "continuation.rkt")

(define havoc-path 'havoc)
(define havoc-𝒾 (-𝒾 'havoc-id havoc-path))

(define x (+x!))
(define 𝐱 (-x x))
(define 𝐱s (list 𝐱))
(define ⟦hv⟧ : -⟦e⟧ (⇓ havoc-path (-ref havoc-𝒾 0)))

(define (arg-● [k : Arity] [i : Integer]) : -⟦e⟧
  (λ (M σ ℒ)
    (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W -●/Vs (-x (+x/memo! 'hv k i))))} ∅ ∅)))

(define (rt-● [k : Arity]) : -⟦e⟧
  (λ (M σ ℒ)
    (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W -●/Vs (-x (+x/memo! 'hv-rt k))))} ∅ ∅)))

(: gen-havoc-Clo : (Listof -module) → -Clo)
;; Generate the unknown context
;; Only used by `verify` module, not `ce`
(define (gen-havoc-Clo ms)

  (define acs (prog-accs ms))

  (define ⟦e⟧ : -⟦e⟧
    (λ (M σ ℒ)
      (for*/ans ([V (σ@ σ (ρ@ (-ℒ-env ℒ) x))])
        (define W (-W¹ V 𝐱))
        (define ⟦V⟧ : -⟦e⟧
          (λ (M σ ℒ)
            (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) 𝐱))} ∅ ∅)))
        (define comp : -⟦e⟧
          (match V
            ;; Ignore first-order and opaque values
            [(or (-●) (? -prim?)) ⊥⟦e⟧]
            
            ;; Give an appropriate number of arguments to function
            [(or (? -Clo?) (? -Case-Clo?) (? -Ar?))
             (define a (V-arity V))

             (define (hv/arity [k : Natural]) : -⟦e⟧
               (define ℓ-V● (+ℓ/memo! 'opq-ap k))
               (define ⟦V-●⟧
                 (cond
                   [(> k 0)
                    (match-define (cons ⟦●⟧₀ ⟦●⟧s) (build-list k (curry arg-● k)))
                    ((↝.@ havoc-path ℓ-V● (list W) ⟦●⟧s) ⟦●⟧₀)]
                   [else    (ap havoc-path ℓ-V● W '())]))
               (define ⟦hv-⟮V-●⟯⟧
                 ((↝.@ havoc-path (+ℓ/memo! 'hv-ap 0) '() (list ⟦V-●⟧)) ⟦hv⟧))
               (define ⟦hv-V⟧
                 ((↝.@ havoc-path (+ℓ/memo! 'hv-ap 1) '() (list ⟦V⟧)) ⟦hv⟧))
               ((↝.begin (list ⟦hv-V⟧)) ⟦hv-⟮V-●⟯⟧))
             
             (match a
               [(arity-at-least k)
                (↝.amb (list (rt-● a) (hv/arity (+ 1 k))))] ; TODO
               [(? integer? k)
                (↝.amb (list (rt-● a) (hv/arity k)))]
               [(? list? ks)
                (define cases : (Listof -⟦e⟧)
                  (for/list ([k ks])
                    (cond [(integer? k) (hv/arity k)]
                          [else (error 'havoc "TODO: ~a" k)])))
                (↝.amb (cons (rt-● a) cases))]
               [_ ⊥⟦e⟧])]

            ;; If it's a struct, havoc all publically accessible fields
            [(or (-St s _) (-St* s _ _ _)) #:when s
             (define ⟦hv-field⟧s : (Listof -⟦e⟧)
               (for/list ([ac (hash-ref acs s →∅)])
                 (define Ac (-W¹ ac ac))
                 (define ⟦ac-V⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'ac-ap ac) (list Ac) '()) ⟦V⟧))
                 (define ⟦hv-⟮ac-V⟯⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'hv-ap ac 0) '() (list ⟦ac-V⟧)) ⟦hv⟧))
                 (define ⟦hv-V⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'hv-ap ac 1) '() (list ⟦V⟧)) ⟦hv⟧))
                 ((↝.begin (list ⟦hv-V⟧)) ⟦hv-⟮ac-V⟯⟧)))
             (↝.amb ⟦hv-field⟧s)]
            
            ;; Havoc vector's content before erasing the vector with unknowns
            ;; Approximate vectors are already erased
            [(-Vector/hetero _ _) ⊥⟦e⟧]
            [(-Vector/homo _ _) ⊥⟦e⟧]
            [(-Vector αs)
             (define ⟦hv-field⟧s : (Listof -⟦e⟧)
               (for/list ([(α i) (in-indexed αs)])
                 (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
                 (define ⟦ac-i⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'vref i) (list Wᵢ -vector-ref/W) '()) ⟦V⟧))
                 (define ⟦hv-⟮ac-i⟯⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'hv-ap 'ref i 0) '() (list ⟦ac-i⟧)) ⟦hv⟧))
                 (define ⟦hv-V⟧
                   ((↝.@ havoc-path (+ℓ/memo! 'hv-ap 'ref i 1) '() (list ⟦V⟧)) ⟦hv⟧))
                 ((↝.begin (list ⟦hv-V⟧)) ⟦hv-⟮ac-i⟯⟧)))
             (↝.amb ⟦hv-field⟧s)]

            ;; Apply contract to unknown values
            [(? -C?)
             (log-warning "TODO: havoc contract combinators")
             ⊥⟦e⟧]))
        (comp M σ ℒ))))

  (-Clo (list x) ⟦e⟧ ⊥ρ ⊤Γ))

(: gen-havoc-exp : (Listof -module) → -e)
;; Generate havoc top-level expression havoc-king modules' exports
(define (gen-havoc-exp ms)
  (define-set refs : -ref)
  
  (for ([m (in-list ms)])
    (match-define (-module path forms) m)
    (for* ([form forms] #:when (-provide? form)
           [spec (-provide-specs form)])
      (match-define (-p/c-item x _ _) spec)
      (refs-add! (-ref (-𝒾 x path) (+ℓ!)))))
  
  (-amb/simp (for/list ([ref (in-set refs)])
               (-@ (•!) (list ref) (+ℓ!)))))

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
