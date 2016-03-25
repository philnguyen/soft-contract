#lang typed/racket/base

(provide gen-havoc-Clo gen-havoc-exp havoc-𝒾)

(require racket/match
         racket/set
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
(define ⟦●⟧ : -⟦e⟧
  (λ (M σ ℒ)
    (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W -●/Vs #f))} ∅ ∅)))
(define ⟦hv⟧ : -⟦e⟧
  (⇓ havoc-path (-ref havoc-𝒾 (+ℓ!))))

(define (ℓₕᵥ [i : Natural]) : -ℓ
  (+ℓ/memo! 'hv-ref i))

(: gen-havoc-Clo : (Listof -module) → -Clo)
;; Generate the unknown context
;; Only used by `verify` module, not `ce`
(define (gen-havoc-Clo ms)

  (define acs-for-struct
    (for/fold ([m : (HashTable -struct-info (℘ -st-ac)) (hash)])
              ([ac (prog-accs ms)])
      (match-define (-st-ac si _) ac)
      (hash-update m si (λ ([acs : (℘ -st-ac)]) (set-add acs ac)) →∅)))

  (define ⟦e⟧ : -⟦e⟧
    (let ()
     
      (λ (M σ ℒ)
        (for*/ans ([V (σ@ σ (ρ@ (-ℒ-env ℒ) x))])
          (define W (-W¹ V 𝐱))
          (define ⟦rt-V⟧ : -⟦e⟧
            (λ (M σ ℒ)
              (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) 𝐱))} ∅ ∅)))
          (define comp : -⟦e⟧
            (match V
              [(or (-●) (? -prim?)) ⊥⟦e⟧] ; ignore first-order and opaque
              [(or (? -Clo?) (? -Ar?) (? -Case-Clo?))
               (define a (V-arity V))
               (define ℓ-V● (+ℓ/memo! 'arity a))

               (define (hv/arity [k : Natural]) : -⟦e⟧
                 (define ⟦V-●⟧
                   (cond
                     [(> k 0) ((↝.@ havoc-path ℓ-V● (list W) (make-list (- k 1) ⟦●⟧)) ⟦●⟧)]
                     [else    (ap havoc-path ℓ-V● W '())]))
                 (define ⟦hv-⸨V-●⸩⟧ ((↝.@ havoc-path (ℓₕᵥ 0) '() (list ⟦V-●⟧)) ⟦hv⟧))
                 (define ⟦hv-V⟧     ((↝.@ havoc-path (ℓₕᵥ 1) '() (list ⟦rt-V⟧)) ⟦hv⟧))
                 (define ⟦hv-⸨V-●⸩∷hv-V⟧ ((↝.begin (list ⟦hv-V⟧)) ⟦hv-⸨V-●⸩⟧))
                 (↝.amb (list ⟦hv-⸨V-●⸩∷hv-V⟧ ⟦●⟧)))
               
               (match a
                 [(arity-at-least k) (hv/arity (+ 1 k))] ; TODO
                 [(? integer? k) (hv/arity k)]
                 [(? list? ks)
                  (↝.amb (for/list : (Listof -⟦e⟧) ([k ks])
                           (cond [(integer? k) (hv/arity k)]
                                 [else (error 'havoc"TODO: ~a" k)])))]
                 [_ ⊥⟦e⟧])

               ]
              [(or (-St s _) (-St* s _ _ _)) #:when s
               (define ⟦hv-field⟧s : (Listof -⟦e⟧)
                 (for/list ([ac (hash-ref acs-for-struct s →∅)])
                   (define Ac (-W¹ ac ac))
                   (define ⟦ac-V⟧      ((↝.@ havoc-path (+ℓ/memo! 'ac ac) (list Ac) '()) ⟦rt-V⟧))
                   (define ⟦hv-⸨ac-V⸩⟧ ((↝.@ havoc-path (ℓₕᵥ 3 #|FIXME|#) '() (list ⟦ac-V⟧)) ⟦hv⟧))
                   (define ⟦hv-V⟧      ((↝.@ havoc-path (ℓₕᵥ 4 #|FIXME|#) '() (list ⟦rt-V⟧)) ⟦hv⟧))
                   ((↝.begin (list ⟦hv-V⟧)) ⟦hv-⸨ac-V⸩⟧)))
               (↝.amb ⟦hv-field⟧s)]
              [(or (? -Vector?) (? -Vector/hetero?) (? -Vector/homo?))
               (log-warning "TODO: havoc vector")
               ⊥⟦e⟧]
              [(? -C?)
               (log-warning "TODO: havoc contract combinators")
               ⊥⟦e⟧]))
          (comp M σ ℒ)))))

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

(: prog-accs : (Listof -module) → (℘ -st-ac))
;; Retrieve set of all public accessors from program
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
  (∪ (for/set: : (℘ -st-ac) ([(x ac) (in-hash defs)] #:when (hash-has-key? decs x))
       ac)
     {set -car -cdr}))
