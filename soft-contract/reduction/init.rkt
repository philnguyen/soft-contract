#lang typed/racket/base

(provide 𝑰)

(require
 racket/match
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "havoc.rkt")
(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)]
  [arr? (Any → Boolean)]
  [arr*? (Any → Boolean)])

;; Load the initial store and havoc-ing expression for given module list
(: 𝑰 : (Listof -module) → (Values -σ -e))
(define (𝑰 ms)
  (define σ₀ (⊔ (acc-decs (acc-defs ⊥σ)) (-α.def havoc-id) (gen-havoc-Clo ms)))
  (define e₀ (gen-havoc-exp ms))
  (values σ₀ e₀))

(: mk-struct-info : Any → -struct-info)
(define (mk-struct-info s)
  (match-let ([`(,(? symbol? t) ,mut?s ...) s])
    (-struct-info
     (-id t 'Λ)
     (length mut?s)
     (for/set: : (℘ Integer) ([(mut? i) (in-indexed mut?s)] #:when mut?) i))))

(: acc-def : Any -σ → -σ)
(define (acc-def d σ)
  (match d
    [`(#:pred ,(? symbol? o) ,_ ...)
     (⊔ σ (-α.def (-id o 'Λ)) o)]
    [`(,(? symbol? o) ,(or (? arr?) (? arr*?)) ,_ ...)
     (⊔ σ (-α.def (-id o 'Λ)) o)]
    [`(#:alias ,_ ,_) #|should have been resolved by parser|# σ]
    [`(#:batch (,os ...) ,_ ...)
     (for/fold ([σ : -σ σ]) ([o os])
       (assert o symbol?)
       (⊔ σ (-α.def (-id o 'Λ)) o))]
    [`(#:struct-cons ,(? symbol? o) ,si)
     (⊔ σ (-α.def (-id o 'Λ)) (-st-mk (mk-struct-info si)))]
    [`(#:struct-pred ,(? symbol? o) ,si)
     (⊔ σ (-α.def (-id o 'Λ)) (-st-p (mk-struct-info si)))]
    [`(#:struct-acc ,(? symbol? o) ,si ,(? exact-nonnegative-integer? i))
     (⊔ σ (-α.def (-id o 'Λ)) (-st-ac (mk-struct-info si) i))]
    [`(#:struct-mut ,(? symbol? o) ,si ,(? exact-nonnegative-integer? i))
     (⊔ σ (-α.def (-id o 'Λ)) (-st-mut (mk-struct-info si) i))]
    [r
     (log-warning "unhandled in `acc-def`: ~a~n" r)
     σ]))

(: acc-defs : -σ → -σ)
(define (acc-defs σ) (foldl acc-def σ prims))

(: acc-dec : Any -σ → -σ)
(define (acc-dec d σ)
  (match d
    [`(#:pred ,(? symbol? o) ,doms? ...)
     (define-values (σ* C c)
       (match doms?
         ['() (values σ 'any/c 'any/c)] ; optimize `(any/c . -> . boolean?)` to `any/c`
         [(list (list dom ...)) ; optimize `boolean?` to `any/c`
          ;(--> s (map (curry simple-parse s) dom) 'any/c)
          (alloc σ '(,@dom . -> . any/c))]))
     (⊔ σ* (-α.ctc (-id o 'Λ)) C)]
    [`(#:alias ,_ ,_) #|should have been resolved by parser|# σ]
    [`(#:batch (,ss ...) ,sig ,_ ...)
     (error 'acc-dec "TODO")]
    [`(,(? symbol? s) ,sig ,_ ...)
     (error 'acc-dec "TODO")]
    [`(#:struct-cons ,s (,_ ,mut?s ...))
     (error 'acc-dec "TODO")]
    [`(#:struct-pred ,s (,_ ,mut? ...))
     (error 'acc-dec "TODO")]
    [`(#:struct-acc ,s ,si ,_)
     (error 'acc-dec "TODO")]
    [`(#:struct-mut ,s ,si ,_)
     (error 'acc-dec "TODO")]
    [r
     (log-warning "unhandled in `acc-dec` ~a~n" r)
     σ]))

(: acc-decs : -σ → -σ)
(define (acc-decs σ) (foldl acc-dec σ prims))

(: alloc : -σ Any → (Values -σ -V -e))
(define (alloc σ s)

  (: alloc-list : -σ (Listof Any) → (Values -σ (Listof -V) (Listof -e)))
  (define (alloc-list σ ss)
    (let loop ([ss : (Listof Any) ss])
      (match ss
        ['() (values σ '() '())]
        [(cons s ss*)
         (define-values (σ₁ V₁ e₁) (alloc σ s))
         (define-values (σₙ Vs es) (alloc-list σ₁ ss*))
         (values σₙ (cons V₁ Vs) (cons e₁ es))])))

  (: alloc-and/c : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
  (define (alloc-and/c σ Cs es)
    (match* (Cs es)
      [('() '())
       (values σ 'any/c 'any/c)]
      [((list C) (list e))
       (values σ C e)]
      [((cons Cₗ Cs*) (cons eₗ es*))
       (define-values (σ* Cᵣ eᵣ) (alloc-and/c σ Cs* es*))
       (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
       (define αₗ (-α.and/c-l eₗ))
       (define αᵣ (-α.and/c-r eᵣ))
       (values (⊔ (⊔ σ* αₗ Cₗ) αᵣ Cᵣ)
               (-And/C flat? αₗ αᵣ)
               (assert (-?@ 'and/c eₗ eᵣ)))]))

  (: alloc-or/c : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
  (define (alloc-or/c σ Cs es)
    (match* (Cs es)
      [('() '())
       (values σ 'none/c 'none/c)]
      [((list C) (list e))
       (values σ C e)]
      [((cons Cₗ Cs*) (cons eₗ es*))
       (define-values (σ* Cᵣ eᵣ) (alloc-or/c σ Cs* es*))
       (define flat? (and (C-flat? Cₗ) (C-flat? Cᵣ)))
       (define αₗ (-α.or/c-l eₗ))
       (define αᵣ (-α.or/c-r eᵣ))
       (values (⊔ (⊔ σ αₗ Cₗ) αᵣ Cᵣ)
               (-Or/C flat? αₗ αᵣ)
               (assert (-?@ 'or/c eₗ eᵣ)))]))

  (match s
    [(? symbol? p)
     (values σ p p)]
    [`(not/c ,c)
     (define-values (σ* C e) (alloc σ c))
     (define α (-α.not/c e))
     (values (⊔ σ* α C)
             (-Not/C α)
             (assert (-?@ 'not/c e)))]
    [`(one-of/c ,c ...)
     (error 'alloc "TODO")]
    [`(and/c ,cs ...)
     (apply/values alloc-and/c (alloc-list σ cs))]
    [`(or/c ,cs ...)
     (apply/values alloc-or/c (alloc-list σ cs))]
    [`(listof ,c)
     (error 'alloc "TODO")]
    [`(list/c ,c ...)
     (error 'alloc "TODO")]
    [`(cons/c ,l ,r)
     (define-values (σ₁ C c) (alloc σ  l))
     (define-values (σ₂ D d) (alloc σ₁ r))
     (define flat? (and (C-flat? C) (C-flat? D)))
     (define α₁ (-α.struct/c c))
     (define α₂ (-α.struct/c d))
     (values (⊔ (⊔ σ₂ α₁ C) α₂ D)
             (-St/C flat? -s-cons (list α₁ α₂))
             (assert (-?@ -cons c d)))]
    [`(,cs ... . -> . ,d)
     (error 'alloc "TODO")]
    [`((,cs ...) #:rest ,d . ->* . ,d)
     (error 'alloc "TODO")]
    [_ 
     (printf "alloc: ignoring ~a~n" s)
     (values σ 'any/c 'any/c)]
    ))
