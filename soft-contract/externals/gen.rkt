#lang typed/racket/base

(provide (for-syntax (all-defined-out))
         (all-from-out "../primitives/gen.rkt"))

(require (for-syntax racket/base
                     racket/match
                     racket/contract
                     racket/syntax
                     syntax/parse
                     "../primitives/utils.rkt")
         racket/match
         racket/contract
         "../utils/map.rkt"
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../primitives/gen.rkt"
         "../proof-relation/main.rkt"
         "def-ext-runtime.rkt")

(begin-for-syntax

  (define-parameter/contract
    [-$ identifier? #f]
    [-ℒ identifier? #f]
    [-⟦k⟧ identifier? #f])

  (define/contract (gen-ans d)
    (syntax? . -> . syntax?)
    #`(error 'gen-ans "TODO: ~a" '#,(syntax->datum d)))

  ;; Generate the expression producing contract `c`
  ;; along with expressions performing neccessary allocations
  (define/contract (gen-alloc ℓ c)
    (identifier? syntax? . -> . syntax?)
    (syntax-parse c
      [((~literal ->) cₓ ... d)
       #`(let ([αℓs (list
                     #,@(for/list ([cₓ (in-list (syntax->list #'(cₓ ...)))]
                                   [i (in-naturals)])
                          #`(let ([⟪α⟫ (-α->-⟪α⟫ '#,cₓ)]
                                  [ℓ (+ℓ/ctc #,ℓ #,i)])
                              (σ⊕! #,(-σ) ⟪α⟫ #,(gen-alloc #'ℓ cₓ))
                              (cons ⟪α⟫ ℓ))))]
               [βℓ
                (let ([⟪β⟫ (-α->-⟪α⟫ 'd)]
                      [ℓ (+ℓ/ctc #,ℓ #,(length (syntax->list #'(cₓ ...))))])
                  (σ⊕! #,(-σ) ⟪β⟫ #,(gen-alloc #'ℓ #'d))
                  (cons ⟪β⟫ ℓ))])
           (-=> αℓs βℓ #,ℓ))]
      [c:id #'(quote c)]
      [_ (error 'gen-alloc "unhandled: ~a" (syntax->datum c))]))

  ;; Generate expression wrapping function contract `c` around identifier `W`
  (define/contract (gen-func-wrap c W)
    (syntax? identifier? . -> . syntax?)
    #`(let* ([ℓ (+ℓ/memo! 'prim '#,(-o))]
             [l³ (-l³ #,(-l) '#,(-o) '#,(-o))]
             [grd #,(gen-alloc #'ℓ c)]
             [s (-W¹-s #,W)]
             [⟪α⟫ (-α->-⟪α⟫ (or (keep-if-const s) (-α.fn #,(-ℒ) ℓ #,(-⟪ℋ⟫))))])
        (σ⊕! #,(-σ) ⟪α⟫ (-W¹-V #,W))
        (-W¹ (-Ar grd ⟪α⟫ l³) s)))

  ;; Generate expression wrapping contract `c` around identifier `W`
  (define/contract (?gen-wrap c W)
    (syntax? identifier? . -> . (or/c #f syntax?))
    (syntax-parse c
      [((~literal ->) _ ...) (gen-func-wrap c W)]
      [_:fc #f]
      [_ (error 'gen-wrap-clause "unhandled: ~a" (syntax->datum #'c))]))

  ;; Generate re-definitions of variables that should be wrapped in higher-order contracts
  (define/contract (gen-arg-wraps body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:hf (-sig))
    (define/with-syntax ([Wᵢ eᵢ] ...)
      (filter values
              (for/list ([W (in-list (-Wₙ))]
                         [c (in-list (attribute sig.init))])
                (define ?rhs (?gen-wrap c W))
                (and ?rhs #`(#,W #,?rhs)))))
    (define/with-syntax (clauses-rest ...) #|TODO|# '())
    `(,@(for/list ([Wᵢ (in-list (syntax->list #'(Wᵢ ...)))]
                   [eᵢ (in-list (syntax->list #'(eᵢ ...)))])
          #`(define #,Wᵢ : -W¹ #,eᵢ))
      ,@body)))
