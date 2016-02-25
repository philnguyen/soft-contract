#lang typed/racket/base

(provide 𝑰)

(require
 racket/match
 "../utils/main.rkt" "../ast/definition.rkt" "../runtime/main.rkt" "havoc.rkt" "step.rkt")
(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)]
  [arr? (Any → Boolean)]
  [arr*? (Any → Boolean)])

;; Temp hack for variable names for independent contracts
(define-parameter indep-prefix : Symbol 'x)

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
          (alloc o σ '(,@dom . -> . any/c))]))
     (⊔ σ* (-α.ctc (-id o 'Λ)) C)]
    [`(#:alias ,_ ,_) #|should have been resolved by parser|# σ]
    [`(#:batch (,(? symbol? ss) ...) ,sig ,_ ...)
     (for/fold ([σ : -σ σ]) ([s ss])
       (acc-dec `(,s ,sig) σ))]
    [`(,(? symbol? s) ,sig ,_ ...)
     (define-values (σ* C c) (alloc s σ sig))
     (⊔ σ* (-α.ctc (-id s 'Λ)) C)]
    [`(#:struct-cons ,s (,_ ,mut?s ...))
     (printf "acc-dec: TODO: constructor ~a~n" s)
     σ]
    [`(#:struct-pred ,s (,_ ,mut? ...))
     (printf "acc-dec: TODO: struct predicate ~a~n" s)
     σ]
    [`(#:struct-acc ,s ,si ,_)
     (printf "acc-dec: TODO: accessor ~a~n" s)
     σ]
    [`(#:struct-mut ,s ,si ,_)
     (printf "acc-dec: TODO: mutator ~a~n" s)
     σ]
    [r
     (log-warning "unhandled in `acc-dec` ~a~n" r)
     σ]))

(: acc-decs : -σ → -σ)
(define (acc-decs σ) (foldl acc-dec σ prims))

(: alloc : Symbol -σ Any → (Values -σ -V -e))
(define (alloc o σ s)
  
  (: simple-parse : Any → -e)
  (define (simple-parse s)
    (match s
      [`(-> ,doms ... ,rng)
       (--> o (map simple-parse doms) (simple-parse rng))]
      [`(->* (,doms ...) #:rest ,rst ,rng)
       (log-warning "Skipping ->* for now~n")
       'any/c]
      [`(and/c ,cs ...) (-and/c 'Λ (map simple-parse cs))]
      [`(or/c  ,cs ...) (-or/c  'Λ (map simple-parse cs))]
      [`(one-of/c ,cs ...) (-one-of/c 'Λ (map simple-parse cs))]
      [`(list/c ,cs ...) (-list/c (map simple-parse cs))]
      [`(cons/c ,c ,d) (-cons/c (simple-parse c) (simple-parse d))]
      [`(not/c ,c) (-not/c 'Λ (simple-parse c))]
      [`(listof ,c) (-listof 'Λ (simple-parse c))]
      [`(values ,ctcs ...)
       (-@ 'values (map simple-parse ctcs) (-src-loc 'Λ (next-loc!)))]
      [(? symbol? s) (-ref (-id s 'Λ) 'Λ (next-loc!))]
      [`(quote ,(? Base? s)) (-b s)]
      [(or (? number? x) (? boolean? x)) (-b x)]))

  (: simple-⇓ : Any → -⟦e⟧)
  (define (simple-⇓ s) (⇓ (simple-parse s)))



  (: alloc-list : -σ (Listof Any) → (Values -σ (Listof -V) (Listof -e)))
  (define (alloc-list σ ss)
    (let loop ([ss : (Listof Any) ss])
      (match ss
        ['() (values σ '() '())]
        [(cons s ss*)
         (define-values (σ₁ V₁ e₁) (alloc o σ s))
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

  (: alloc-list/c : -σ (Listof -V) (Listof -e) → (Values -σ -V -e))
  (define (alloc-list/c σ Cs es)
    (match* (Cs es)
      [('() '()) (values σ 'null? 'null?)]
      [((cons Cₗ Cs*) (cons eₗ es*))
       (define-values (σ* Cᵣ eᵣ) (alloc-list/c σ Cs* es*))
       (define αₗ (-α.struct/c eₗ))
       (define αᵣ (-α.struct/c eᵣ))
       (values (⊔ (⊔ σ* αₗ Cₗ) αᵣ Cᵣ)
               (-St/C (and (C-flat? Cₗ) (C-flat? Cᵣ)) -s-cons (list αₗ αᵣ))
               (assert (-?struct/c -s-cons (list eₗ eᵣ))))]))

  (match s
    [(? symbol? p)
     (values σ p p)]
    [`(not/c ,c)
     (define-values (σ* C e) (alloc o σ c))
     (define α (-α.not/c e))
     (values (⊔ σ* α C)
             (-Not/C α)
             (assert (-?@ 'not/c e)))]
    [`(one-of/c ,c ...)
     (printf "TODO: 'alloc one-of/c~n")
     (values σ 'any/c 'any/c)]
    [`(and/c ,cs ...)
     (apply/values alloc-and/c (alloc-list σ cs))]
    [`(or/c ,cs ...)
     (apply/values alloc-or/c (alloc-list σ cs))]
    [`(listof ,c)
     (printf "TODO: 'alloc list/c~n")
     (values σ 'any/c 'any/c)]
    [`(list/c ,cs ...)
     (apply/values alloc-list/c (alloc-list σ cs))]
    [`(cons/c ,l ,r)
     (define-values (σ₁ C c) (alloc o σ  l))
     (define-values (σ₂ D d) (alloc o σ₁ r))
     (define flat? (and (C-flat? C) (C-flat? D)))
     (define α₁ (-α.struct/c c))
     (define α₂ (-α.struct/c d))
     (values (⊔ (⊔ σ₂ α₁ C) α₂ D)
             (-St/C flat? -s-cons (list α₁ α₂))
             (assert (-?struct/c -s-cons (list c d))))]
    [`(,ss ... . -> . ,d)
     (define-values (σ₁ Cs cs) (alloc-list σ ss))
     (define ⟦d⟧ (simple-⇓ d))
     (define-values (σ₂ doms-rev xs-rev)
       (let ([x (indep-prefix)])
         (for/fold ([σ₂ : -σ σ₁] [doms-rev : (Listof (Pairof Symbol -α.dom)) '()] [xs-rev : (Listof Symbol) '()])
                   ([C Cs] [(c i) (in-indexed cs)])
           (define α (-α.dom c))
           (define xi (string->symbol (format "~a~a" x (n-sub i))))
           (values (⊔ σ₂ α C) (cons (cons xi α) doms-rev) (cons xi xs-rev)))))
     (define doms (reverse doms-rev))
     (define xs (reverse xs-rev))
     (define C (-=>i doms #f ⟦d⟧ ⊥ρ))
     (define c (assert (-?->i xs cs (simple-parse d))))
     (values σ₂ C c)]
    [`((,cs ...) #:rest ,d . ->* . ,d)
     (printf "TODO: alloc ->*~n")
     (values σ 'any/c 'any/c)]
    [_ 
     (printf "alloc: ignoring ~a~n" s)
     (values σ 'any/c 'any/c)]
    ))
