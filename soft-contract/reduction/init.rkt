#lang typed/racket/base

(provide 𝑰)

(require racket/match
         racket/set
         racket/list
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/widen.rkt"
         "havoc.rkt")
(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)]
  [arr? (Any → Boolean)]
  [arr*? (Any → Boolean)])

(: 𝑰 : (Listof -module) → (Values -σ -e))
;; Load the initial store and havoc-ing expression for given module list
(define (𝑰 ms)
  (define e† (gen-havoc-exp ms))
  (define hv (gen-havoc-clo ms))
  (define σ (σ₀))
  (σ⊕*! σ [(-α->-⟪α⟫ (-α.def havoc-𝒾)) ↦ hv]
          [(-α->-⟪α⟫ (-α.wrp havoc-𝒾)) ↦ hv])
  ;(ensure-singletons σ) ; disable this in production
  (values σ e†))

(define -⟦boolean?⟧ : -⟦e⟧!
  (λ (ρ $ Γ 𝒞 Σ ⟦k⟧)
    (⟦k⟧ (-W (list 'boolean?) 'boolean?) $ Γ 𝒞 Σ)))
(define -⟦any/c⟧ : -⟦e⟧!
  (λ (ρ $ Γ 𝒞 Σ ⟦k⟧)
    (⟦k⟧ (-W (list 'any/c) 'any/c) $ Γ 𝒞 Σ)))
(define -⟦void?⟧ : -⟦e⟧!
  (λ (ρ $ Γ 𝒞 Σ ⟦k⟧)
    (⟦k⟧ (-W (list 'void?) 'void?) $ Γ 𝒞 Σ)))

(: alloc! : -σ Any → Void)
;; Allocate primitives wrapped with contracts.
;; Positive components can be optimized away because we assume primitives are correct.
(define (alloc! σ s)
  (match s
    [`(#:pred ,(? symbol? o))
     (define-values (C c) (alloc-C! σ '(any/c . -> . boolean?)))
     (alloc-Ar-o! σ o (assert C -=>?) (assert c -->?))]
    [`(#:pred ,(? symbol? o) (,cs ...))
     (define-values (C c) (alloc-C! σ `(,@cs . -> . boolean?)))
     (alloc-Ar-o! σ o (assert C -=>?) (assert c -->?))]
    [`(#:alias ,_  ,_) ; should have been taken care of by parser
     (void)]
    [`(#:batch (,os ...) ,(? arr? sig) ,_ ...)
     (define-values (C c) (alloc-C! σ sig))
     (assert C -=>?)
     (assert c -->?)
     (for ([o os])
       (alloc-Ar-o! σ (assert o symbol?) C c))]
    [`(,(? symbol? o) ,(? arr? sig) ,_ ...)
     (define-values (C c) (alloc-C! σ sig))
     (alloc-Ar-o! σ o (assert C -=>?) (assert c -->?))]
    [`(,(? symbol? o) ,(? arr*? sig) ...)
     (log-warning "TODO: ->* for ~a~n" o)
     (σ⊕*! σ [(-α->-⟪α⟫ (-α.def (-𝒾 o 'Λ))) ↦ o]
             [(-α->-⟪α⟫ (-α.wrp (-𝒾 o 'Λ))) ↦ o])]
    [`(,(? symbol? o) ,_ ...) (void)]
    [`(#:struct-cons ,(? symbol? o) (,(? symbol? t) ,mut?s ...))
     (define 𝒾 (-𝒾 t 'Λ))
     (alloc-Ar! σ o (-st-mk 𝒾) (make-list (length mut?s) 'any/c) (-st-p 𝒾))]
    [`(#:struct-pred ,(? symbol? o) (,(? symbol? t) ,_ ...))
     (define 𝒾 (-𝒾 t 'Λ))
     (alloc-Ar! σ o (-st-p 𝒾) (list 'any/c) 'boolean?)]
    [`(#:struct-acc ,(? symbol? o) (,(? symbol? t) ,_ ...) ,(? index? i))
     (define 𝒾 (-𝒾 t 'Λ))
     (alloc-Ar! σ o (-st-ac 𝒾 i) (list (-st-p 𝒾)) 'any/c)]
    [`(#:struct-mut ,(? symbol? o) (,(? symbol? t) ,_ ...) ,(? index? i))
     (define 𝒾 (-𝒾 t 'Λ))
     (alloc-Ar! σ o (-st-mut 𝒾 i) (list (-st-p 𝒾) 'any/c) 'void?)]))

(: alloc-Ar-o! : -σ Symbol -=> -e → Void)
;; Allocate wrapped and unwrapped version of primitive `o` in store `σ`
(define (alloc-Ar-o! σ o C c)
  (define-values (α₀ α₁)
    (let ([𝒾 (-𝒾 o 'Λ)])
      (values (-α->-⟪α⟫ (-α.def 𝒾)) (-α->-⟪α⟫ (-α.wrp 𝒾)))))
  (case o
    #;[(make-sequence) ; FIXME tmp hack
     (σ⊕*! σ [α₀ ↦ o] [α₁ ↦ o])]
    [else
     (define O (-Ar C α₀ (-l³ o 'dummy o)))
     (σ⊕*! σ [α₀ ↦ o] [α₁ ↦ O])]))

(: alloc-Ar! : -σ Symbol -o (Listof -prim) -prim → Void)
;; Allocate unsafe and (non-dependently) contracted versions of operator `o` at name `s`
(define (alloc-Ar! σ s o cs d)
  (define-values (α₀ α₁)
    (let ([𝒾 (-𝒾 s 'Λ)])
      (values (-α->-⟪α⟫ (-α.def 𝒾)) (-α->-⟪α⟫ (-α.wrp 𝒾)))))
  (define αs (alloc-prims! σ cs))
  (define β  (alloc-prim!  σ d))
  (define αℓs : (Listof (Pairof -⟪α⟫ -ℓ))
    (for/list ([α : -⟪α⟫ αs])
      (cons α (+ℓ!))))
  (define βℓ (cons β (+ℓ!)))
  (define C (-=> αℓs βℓ (+ℓ!)))
  (define O (-Ar C α₀ (-l³ (show-o o) 'dummy (show-o o))))
  (σ⊕*! σ [α₀ ↦ o] [α₁ ↦ O]))

(: alloc-C! : -σ Any → (Values -V -e))
;; "Evaluate" restricted contract forms
(define (alloc-C! σ s)
  (match s
    [(? symbol? s)
     (case s ; tmp HACK
       [(cons? pair?) (values -cons? s)]
       [(box?) (values -box? s)]
       [else (values s s)])]
    [`(not/c ,s*)
     (define-values (C* c*) (alloc-C! σ s*))
     (define α* (alloc-const! σ C* c*))
     (define ℓ (+ℓ!))
     (values (-Not/C (cons α* ℓ)) (-@ 'not/c (list c*) ℓ))]
    [`(one-of/c ,ss ...)
     (log-warning "TODO: one-of/c~n")
     (values 'any/c 'any/c)]
    [`(and/c ,ss ...)
     (define-values (Cs cs) (alloc-Cs! σ ss))
     (alloc-And/C! σ Cs cs)]
    [`(or/c ,ss ...)
     (define-values (Cs cs) (alloc-Cs! σ ss))
     (alloc-Or/C! σ Cs cs)]
    [`(cons/c ,s₁ ,s₂)
     (define-values (C c) (alloc-C! σ s₁))
     (define-values (D d) (alloc-C! σ s₂))
     (define flat? (and (C-flat? C) (C-flat? D)))
     (define α₁ (-α->-⟪α⟫ c))
     (define α₂ (-α->-⟪α⟫ d))
     (σ⊕*! σ [α₁ ↦ C] [α₂ ↦ D])
     (values (-St/C flat? -𝒾-cons (list (cons α₁ (+ℓ!)) (cons α₂ (+ℓ!))))
             (-struct/c -𝒾-cons (list c d) (+ℓ!)))]
    [`(listof ,s*)
     (log-warning "TODO: alloc 'listof~n")
     (values 'any/c 'any/c)]
    [`(list/c ,ss ...)
     (define-values (Cs cs) (alloc-Cs! σ ss))
     (alloc-List/C! σ Cs cs)]
    [`(,doms ... . -> . ,rng)
     (define-values (Cs cs) (alloc-Cs! σ doms))
     (define αs (alloc-consts! σ Cs cs))
     (define-values (D d) (alloc-C! σ rng))
     (define β (alloc-const! σ D d))
     (define ℓ (+ℓ!))
     (define αℓs : (Listof (Pairof -⟪α⟫ -ℓ))
       (for/list ([α : -⟪α⟫ αs]) (cons α (+ℓ!))))
     (define βℓ (cons β (+ℓ!)))
     (values (-=> αℓs βℓ ℓ) (--> cs d ℓ))]
    [`((,doms ...) #:rest ,rst . ->* . d)
     (log-warning "TODO: alloc ->*~n")
     (values 'any/c 'any/c)]
    [s
     (log-warning "alloc: ignoring ~a~n" s)
     (values 'any/c 'any/c)]))

(: alloc-Cs! : -σ (Listof Any) → (Values (Listof -V) (Listof -e)))
(define (alloc-Cs! σ ss)
  (let go! ([ss : (Listof Any) ss])
    (match ss
      ['() (values '() '())]
      [(cons s ss*)
       (define-values (C₁ c₁) (alloc-C!  σ s  ))
       (define-values (Cs cs) (alloc-Cs! σ ss*))
       (values (cons C₁ Cs) (cons c₁ cs))])))

(: alloc-And/C! : -σ (Listof -V) (Listof -e) → (Values -V -e))
(define (alloc-And/C! σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values 'any/c 'any/c)]
    [((list C) (list c))
     (values C c)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (Cᵣ cᵣ) (alloc-And/C! σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (define αₗ (alloc-const! σ Cₗ cₗ))
     (define αᵣ (alloc-const! σ Cᵣ cᵣ))
     #;(σ⊕*! σ [cₗ ↦ Cₗ] [cᵣ ↦ Cᵣ])
     (values (-And/C flat? (cons αₗ (+ℓ!)) (cons αᵣ (+ℓ!)))
             (-@ 'and/c (list cₗ cᵣ) (+ℓ!)))]))

(: alloc-Or/C! : -σ (Listof -V) (Listof -e) → (Values -V -e))
(define (alloc-Or/C! σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values 'none/c 'none/c)]
    [((list C) (list c))
     (values C c)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (Cᵣ cᵣ) (alloc-Or/C! σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (define αₗ (alloc-const! σ Cₗ cₗ))
     (define αᵣ (alloc-const! σ Cᵣ cᵣ))
     (values (-Or/C flat? (cons αₗ (+ℓ!)) (cons αᵣ (+ℓ!)))
             (-@ 'or/c (list cₗ cᵣ) (+ℓ!)))]))

(: alloc-List/C! : -σ (Listof -V) (Listof -e) → (Values -V -e))
(define (alloc-List/C! σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values 'null? 'null?)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (Cᵣ cᵣ) (alloc-List/C! σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (define αₗ (alloc-const! σ Cₗ cₗ))
     (define αᵣ (alloc-const! σ Cᵣ cᵣ))
     (values (-St/C flat? -𝒾-cons (list (cons αₗ (+ℓ!)) (cons αᵣ (+ℓ!))))
             (-struct/c -𝒾-cons (list cₗ cᵣ) (+ℓ!)))]))

(: alloc-prim! : -σ -prim → -⟪α⟫)
(define (alloc-prim! σ p)
  (alloc-const! σ p p))

(: alloc-prims! : -σ (Listof -prim) → (Listof -⟪α⟫))
(define (alloc-prims! σ ps)
  (alloc-consts! σ ps ps))

(: alloc-const! : -σ -V -e → -⟪α⟫)
;; Allocate value `V` known to have been evaluted to by constant expression `e`
;; This is used internally for `Λ` module only to reduce ridiculous allocation
(define (alloc-const! σ V v)
  (case V ; tmp HACK
    [(cons? pair?)
     (define ⟪α⟫ (-α->-⟪α⟫ -cons?))
     (σ⊕! σ ⟪α⟫ -cons?)
     ⟪α⟫]
    [(box?)
     (define ⟪α⟫ (-α->-⟪α⟫ -box?))
     (σ⊕! σ ⟪α⟫ -box?)
     ⟪α⟫]
    [else
     (define ⟪α⟫ (-α->-⟪α⟫ v))
     (σ⊕! σ ⟪α⟫ V)
     ⟪α⟫]))

(: alloc-consts! : -σ (Listof -V) (Listof -e) → (Listof -⟪α⟫))
;; Allocate values `Vs` known to have been evaluated by constant expressions `es`
;; This is used internally for `Λ` module only to reduce ridiculous allocation.
(define (alloc-consts! σ Vs es)
  (for/list ([V Vs] [e es])
    (alloc-const! σ V e)))

(define (σ₀)
  (define σ (⊥σ))
  (for ([dec prims])
    (alloc! σ dec))
  σ)

(require racket/string)
(define (ensure-singletons [σ : -σ]) : Void
  (define m (-σ-m σ))
  (for* ([(k vs) m] #:when (> (set-count vs) 1))
    (define s
      (string-join
       (for/list : (Listof String) ([v vs])
         (format " - ~a" (show-V v)))
       "\n"
       #:before-first (format "~a (~a):~n" k (set-count vs))))
    (error s)))
