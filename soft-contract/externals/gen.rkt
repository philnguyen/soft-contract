#lang typed/racket/base

(provide (for-syntax (all-defined-out))
         (all-from-out "../primitives/gen.rkt"))

(require (for-syntax racket/base
                     racket/match
                     racket/contract
                     racket/syntax
                     syntax/parse
                     "../primitives/utils.rkt")
         racket/set
         racket/match
         racket/contract
         "../utils/map.rkt"
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../ast/shorthands.rkt"
         "../ast/srcloc.rkt"
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
                          #`(let ([⟪α⟫ (-α->⟪α⟫ '#,cₓ)]
                                  [ℓ (ℓ-with-id #,ℓ #,i)])
                              (σ⊕! #,(-Σ) ⟪α⟫ #,(gen-alloc #'ℓ cₓ))
                              (cons ⟪α⟫ ℓ))))]
               [βℓ
                (let ([⟪β⟫ (-α->⟪α⟫ 'd)]
                      [ℓ (ℓ-with-id #,ℓ #,(length (syntax->list #'(cₓ ...))))])
                  (σ⊕! #,(-Σ) ⟪β⟫ #,(gen-alloc #'ℓ #'d))
                  (cons ⟪β⟫ ℓ))])
           (-=> αℓs βℓ #,ℓ))]
      [c:id #'(quote c)]
      [_ (error 'gen-alloc "unhandled: ~a" (syntax->datum c))]))

  ;; Generate expression wrapping function contract `c` around `V`
  (define/contract (gen-func-wrap c V s)
    (syntax? syntax? syntax? . -> . syntax?)
    ;; be careful not to use `V` twice
    #`(let* ([ℓ (loc->ℓ (loc '#,(-o) 0 0 '()))]
             [l³ (-l³ #,(-l) '#,(-o) '#,(-o))]
             [grd #,(gen-alloc #'ℓ c)]
             [⟪α⟫ (-α->⟪α⟫ (or (keep-if-const #,s)
                               (-α.fn #,(-ℒ) #,(-⟪ℋ⟫) (-Γ-facts #,(-Γ)))))])
        (σ⊕! #,(-Σ) ⟪α⟫ #,V)
        (-Ar grd ⟪α⟫ l³)))

  ;; Generate expression wrapping contract `c` around `V`
  (define/contract (gen-wrap c V s)
    (syntax? syntax? syntax? . -> . syntax?)
    ;; be careful not to use `V` twice
    (syntax-parse c
      [((~literal ->) _ ...) (gen-func-wrap c V s)]
      [((~literal and/c) c*:id ...) #`(V+ #,(-σ) #,V (seteq 'c* ...))]
      ;[((~literal and/c) c*    ...) (foldr gen-wrap V (syntax->list #'(c* ...)))]
      [c:id #`(V+ #,(-σ) #,V 'c)]
      [_ (error 'gen-wrap-clause "unhandled: ~a" (syntax->datum #'c))]))

  ;; Generate re-definitions of variables that should be wrapped in higher-order contracts
  (define/contract (gen-arg-wraps body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:hf (-sig))
    (define eᵢs
      (for/list ([W (in-list (-Wₙ))]
                 [c (in-list (attribute sig.init))])
        (gen-wrap c #`(-W¹-V #,W) #`(-W¹-s #,W))))
    (define/with-syntax (clauses-rest ...) #|TODO|# '())
    (list
     #`(let (#,@(for/list ([Wᵢ (in-list (-Wₙ))]
                           [eᵢ (in-list eᵢs)])
                  #`[#,Wᵢ (-W¹ #,eᵢ (-W¹-s #,Wᵢ))])
             clauses-rest ...)
         #,@body))))
