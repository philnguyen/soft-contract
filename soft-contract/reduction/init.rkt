#lang typed/racket/base

(provide 𝑰 σ₀)

(require racket/match
         racket/set
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         ;"havoc.rkt"
         (only-in "step.rkt" [⇓ ⇓/l])
         "continuation.rkt"
         "havoc.rkt")
(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)]
  [arr? (Any → Boolean)]
  [arr*? (Any → Boolean)])

(: 𝑰 : (Listof -module) → (Values -σ -e))
;; Load the initial store and havoc-ing expression for given module list
(define (𝑰 ms)
  (define e† (gen-havoc-exp ms))
  (define hv (gen-havoc-Clo ms))
  (values (⊔ σ₀ (-α.def havoc-𝒾) hv) e†))

(: ⇓ : -e → -⟦e⟧)
(define (⇓ e) (⇓/l 'Λ e))

(define -⟦boolean?⟧ (⇓ (-𝒾 'boolean? 'Λ)))
(define -⟦any/c⟧ (⇓ (-𝒾 'any/c 'Λ)))
(define -⟦void?⟧ (⇓ (-𝒾 'void? 'Λ)))
;(define -l³-dummy (Mon-Info 'Λ 'dummy 'Λ))

(: alloc : -σ Any → -σ)
;; Allocate primitives wrapped with contracts.
;; Positive components can be optimized away because we assume primitives are correct.
(define (alloc σ s)
  (match s
    [`(#:pred ,(? symbol? o))
     (define-values (σ* C c) (alloc-C σ '(any/c . -> . boolean?)))
     (alloc-Ar-o σ* o (assert C -=>?) (assert c -->?))]
    [`(#:pred ,(? symbol? o) (,cs ...))
     (define-values (σ* C c) (alloc-C σ `(,@cs . -> . boolean?)))
     (alloc-Ar-o σ* o (assert C -=>?) (assert c -->?))]
    [`(#:alias ,_  ,_) ; should have been taken care of by parser
     σ]
    [`(#:batch (,os ...) ,(? arr? sig) ,_ ...)
     (define-values (σ* C c) (alloc-C σ sig))
     (assert C -=>?)
     (assert c -->?)
     (for/fold ([σ* : -σ σ*]) ([o os])
       (alloc-Ar-o σ* (assert o symbol?) C c))]
    [`(,(? symbol? o) ,(? arr? sig) ,_ ...)
     (define-values (σ* C c) (alloc-C σ sig))
     (alloc-Ar-o σ* o (assert C -=>?) (assert c -->?))]
    [`(,(? symbol? o) ,(? arr*? sig) ...)
     (log-warning "TODO: ->* for ~a~n" o)
     (⊔* σ [(-α.def (-𝒾 o 'Λ)) o] [(-α.wrp (-𝒾 o 'Λ)) o])]
    [`(,(? symbol? o) ,_ ...) σ]
    [`(#:struct-cons ,(? symbol? o) ,si)
     (define s (mk-struct-info si))
     (alloc-Ar σ o (-st-mk s) (make-list (-struct-info-arity s) 'any/c) (-st-p s))]
    [`(#:struct-pred ,(? symbol? o) ,si)
     (define s (mk-struct-info si))
     (alloc-Ar σ o (-st-p s) (list 'any/c) 'boolean?)]
    [`(#:struct-acc ,(? symbol? o) ,si ,(? exact-nonnegative-integer? i))
     (define s (mk-struct-info si))
     (alloc-Ar σ o (-st-ac s i) (list (-st-p s)) 'any/c)]
    [`(#:struct-mut ,(? symbol? o) ,si ,(? exact-nonnegative-integer? i))
     (define s (mk-struct-info si))
     (alloc-Ar σ o (-st-mut s i) (list (-st-p s) 'any/c) 'void?)]))

(: alloc-Ar-o : -σ Symbol -=> -e → -σ)
;; Allocate wrapped and unwrapped version of primitive `o` in store `σ`
(define (alloc-Ar-o σ o C c)
  (define-values (α₀ α₁)
    (let ([𝒾 (-𝒾 o 'Λ)])
      (values (-α.def 𝒾) (-α.wrp 𝒾))))
  (define O (-Ar C α₀ (Mon-Info o 'dummy o)))
  (⊔* σ [α₀ o] [α₁ O]))

(: alloc-Ar : -σ Symbol -o (Listof -prim) -prim → -σ)
;; Allocate unsafe and (non-dependently) contracted versions of operator `o` at name `s`
(define (alloc-Ar σ s o cs d)
  (define-values (α₀ α₁)
    (let ([𝒾 (-𝒾 s 'Λ)])
      (values (-α.def 𝒾) (-α.wrp 𝒾))))
  (define-values (σ₁ αs) (alloc-prims σ cs))
  (define-values (σ₂ β ) (alloc-prim  σ₁ d))
  (define C (-=> αs β (+ℓ!)))
  (define O (-Ar C α₀ (Mon-Info (show-o o) 'dummy (show-o o))))
  (⊔* σ₂ [α₀ o] [α₁ O]))

(: alloc-C : -σ Any → (Values -σ -V -e))
;; "Evaluate" restricted contract forms
(define (alloc-C σ s)
  (match s
    [(? symbol? s) (values σ s s)]
    [`(not/c ,s*)
     (define-values (σ₁ C* c*) (alloc-C σ s*))
     (define σ₂ (⊔ σ₁ c* C*))
     (values σ₂ (-Not/C c*) (-not/c c*))]
    [`(one-of/c ,ss ...)
     (log-warning "TODO: one-of/c~n")
     (values σ 'any/c 'any/c)]
    [`(and/c ,ss ...)
     (apply/values alloc-And/C (alloc-Cs σ ss))]
    [`(or/c ,ss ...)
     (apply/values alloc-Or/C  (alloc-Cs σ ss))]
    [`(cons/c ,s₁ ,s₂)
     (define-values (σ₁ C c) (alloc-C σ  s₁))
     (define-values (σ₂ D d) (alloc-C σ₁ s₂))
     (define flat? (and (C-flat? C) (C-flat? D)))
     (values (⊔* σ₂ [c C] [d D])
             (-St/C flat? -s-cons (list c d))
             (assert (-?struct/c -s-cons (list c d))))]
    [`(listof ,s*)
     (log-warning "TODO: alloc 'listof~n")
     (values σ 'any/c 'any/c)]
    [`(list/c ,ss ...)
     (apply/values alloc-List/C (alloc-Cs σ ss))]
    [`(,doms ... . -> . ,rng)
     (define-values (σ₁ Cs cs) (alloc-Cs σ doms))
     (define-values (σ₂ αs) (alloc-consts σ₁ Cs cs))
     (define-values (σ₃ D d) (alloc-C σ₂ rng))
     (define-values (σ₄ β) (alloc-const σ₃ D d))
     (define C (-=> αs β (+ℓ!)))
     (define c (--> cs d 0))
     (values σ₄ C c)]
    [`((,doms ...) #:rest ,rst . ->* . d)
     (log-warning "TODO: alloc ->*~n")
     (values σ 'any/c 'any/c)]
    [s
     (log-warning "alloc: ignoring ~a~n" s)
     (values σ 'any/c 'any/c)]))

(: alloc-Cs : -σ (Listof Any) → (Values -σ (Listof -V) (Listof -e)))
(define (alloc-Cs σ ss)
  (let go ([ss : (Listof Any) ss])
    (match ss
      ['() (values σ '() '())]
      [(cons s ss*)
       (define-values (σ₁ C₁ c₁) (alloc-C  σ  s  ))
       (define-values (σₙ Cs cs) (alloc-Cs σ₁ ss*))
       (values σₙ (cons C₁ Cs) (cons c₁ cs))])))

(: alloc-And/C : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
(define (alloc-And/C σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values σ 'any/c 'any/c)]
    [((list C) (list c))
     (values σ C c)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (σ* Cᵣ cᵣ) (alloc-And/C σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (values (⊔* σ* [cₗ Cₗ] [cᵣ Cᵣ])
             (-And/C flat? cₗ cᵣ)
             (assert (-?@ 'and/c cₗ cᵣ)))]))

(: alloc-Or/C : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
(define (alloc-Or/C σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values σ 'none/c 'none/c)]
    [((list C) (list c))
     (values σ C c)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (σ* Cᵣ cᵣ) (alloc-Or/C σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (values (⊔* σ* [cₗ Cₗ] [cᵣ Cᵣ])
             (-Or/C flat? cₗ cᵣ)
             (assert (-?@ 'or/c cₗ cᵣ)))]))

(: alloc-List/C : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
(define (alloc-List/C σ Cs cs)
  (match* (Cs cs)
    [('() '())
     (values σ 'null? 'null?)]
    [((cons Cₗ Cs*) (cons cₗ cs*))
     (define-values (σ* Cᵣ cᵣ) (alloc-List/C σ Cs* cs*))
     (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
     (values (⊔* σ* [cₗ Cₗ] [cᵣ Cᵣ])
             (-St/C flat? -s-cons (list cₗ cᵣ))
             (assert (-?struct/c -s-cons (list cₗ cᵣ))))]))

(: alloc-prim : -σ -prim → (Values -σ -α.cnst))
(define (alloc-prim σ p)
  (alloc-const σ p p))

(: alloc-prims : -σ (Listof -prim) → (Values -σ (Listof -α.cnst)))
(define (alloc-prims σ ps)
  (alloc-consts σ ps ps))

(: alloc-const : -σ -V -e → (Values -σ -α.cnst))
;; Allocate value `V` known to have been evaluted to by constant expression `e`
;; This is used internally for `Λ` module only to reduce ridiculous allocation
(define (alloc-const σ V v)
  (values (⊔ σ v V) v))

(: alloc-consts : -σ (Listof -V) (Listof -e) → (Values -σ (Listof -α.cnst)))
;; Allocate values `Vs` known to have been evaluated by constant expressions `es`
;; This is used internally for `Λ` module only to reduce ridiculous allocation.
(define (alloc-consts σ Vs es)
  (define-values (σ* αs-rev)
    (for/fold ([σ : -σ σ] [αs-rev : (Listof -α.cnst) '()])
              ([V Vs] [e es])
      (define-values (σ* α) (values (⊔ σ e V) e))
      (values σ* (cons α αs-rev))))
  (values σ* (reverse αs-rev)))

(: simple-parse : Any → -e)
;; Parse + compile restricted form of contracts given in Sexp
(define simple-parse
  (match-lambda
    [(? symbol? o) o]
    [`(quote ,(? Base? s)) (-b s)]
    [(and x (or (? number?) (? boolean?))) (-b x)]
    [`(not/c ,s) (-not/c (simple-parse s))]
    [`(one-of/c ,ss ...) (-one-of/c (map simple-parse ss))]
    [`(and/c ,ss ...) (-and/c (map simple-parse ss))]
    [`(or/c ,ss ...) (-and/c (map simple-parse ss))]
    [`(listof ,s) (-listof (simple-parse s))]
    [`(list/c ,ss ...) (-list/c (map simple-parse ss))]
    [`(cons/c ,l ,r) (-cons/c (simple-parse l) (simple-parse r))]
    [`(,cs ... . -> . ,d)
     (--> (map simple-parse cs) (simple-parse d) 0)]
    [`(values ,ss ...)
     (-@ 'values (map simple-parse ss) 0)]
    [s 
     (error 'simple-parse "unexpected: ~a" s)]))

(: mk-struct-info : Any → -struct-info)
(define (mk-struct-info s)
  (match-let ([`(,(? symbol? t) ,mut?s ...) s])
    (-struct-info
     (-𝒾 t 'Λ)
     (length mut?s)
     (for/set: : (℘ Natural) ([mut? mut?s] [i : Natural (in-naturals)] #:when mut?)
       i))))

(define σ₀
  (for/fold ([σ : -σ ⊥σ]) ([dec prims])
    (alloc σ dec)))
