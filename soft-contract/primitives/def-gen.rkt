#lang typed/racket/base

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/function
                     racket/contract
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "def-utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/list
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(begin-for-syntax

  (define-syntax-rule (with-hack:make-available (src id ...) e ...)
    (with-syntax ([id (format-id src "~a" 'id)] ...) e ...))

  (define-syntax-rule (hack:make-available src id ...)
    (begin (define/with-syntax id (format-id src "~a" 'id)) ...))

  ;; Global parameters that need to be set up for each `def`
  (define-parameter/contract
    ; identifiers available to function body
    [-o identifier? #f]
    [-ℓ identifier? #f]
    [-Ws identifier? #f]
    [-⟪ℋ⟫ identifier? #f]
    [-$ identifier? #f]
    [-Γ identifier? #f]
    [-Σ identifier? #f]
    [-⟦k⟧ identifier? #f]
    [-sig syntax? #f]
    [-Wⁿ (listof identifier?) #f]
    [-Wᵣ (or/c #f identifier?) #f]
    [-gen-lift? boolean? #f]
    [-refinements (listof syntax?) '()]
    )

  #;(define/contract (gen-domain-checks body)
    ((listof syntax?) . -> . (listof syntax?))
    (define/syntax-parse sig:hc (-sig))

      (define arity-check-cases
        (let go ([sig #'sig])
        (syntax-parse sig
          [((~literal ->) c ... _)
           (list
            #`[(list #,@(take (-Wⁿ) (syntax-length #'(c ...))))
               #,@(gen-case-check (syntax->list #'(c ...)) #f (list #'(on-args-ok)))])]
          [((~literal ->*) c ... #:rest r _)
           (list
            #`[(list* #,@(take (-Wⁿ) (syntax-length #'(c ...))) #,(-Wᵣ))
               #,@(gen-case-check (syntax->list #'(c ...) #'r (list #'(on-args-ok))))])]
          [((~literal case->) clauses ...)
           (for/list ([clause (in-syntax-list #'(clauses ...))])
             (syntax-parse clause
               [((~literal ->) c ... #:rest r _)
                #`[(list* #,@(take (-Wⁿ) (syntax-length #'(c ...))) #,(-Wᵣ))
                   #,@(gen-case-check (syntax->list #'(c ...)) #'r (list #'(on-args-ok)))]]
               [((~literal ->) c ... _)
                #`[(list #,@(take (-Wⁿ) (syntax-length #'(c ...))))
                   #,@(gen-case-check (syntax->list #'(c ...)) #f (list #'(on-args-ok)))]]))]
          [((~literal ∀/c) _ c) (go #'c)])))

    (define/with-syntax error-msg (string->symbol (format "arity ~v" (attribute sig.arity))))
    (list
     #`(define (on-args-ok) #,@body)
     #`(match #,(-Ws)
         #,@arity-check-cases
         [_
          (define blm (-blm (ℓ-src #,(-ℓ)) '#,(-o) (list 'error-msg) (map -W¹-V #,(-Ws)) #,(-ℓ)))
          (#,(-⟦k⟧) blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))])))

  #;(define/contract (gen-range-assumptions)
    (-> (listof syntax?))
    (list
     #`(error 'gen-range-assumptions "TODO")))

  #;(define/contract (gen-lift body)
    ((listof syntax?) . -> . (listof syntax?))
    (list*
     #`(error 'gen-lift "TODO")
     body))

  #;(define/contract (gen-refinements body)
    ((listof syntax?) . -> . (listof syntax?))
    (list*
     #`(error 'gen-refinements "TODO")
     body))

  #;(define/contract (gen-case-check inits ?rest body)
    ((listof syntax?) (or/c #f syntax?) (listof syntax?) . -> . (listof syntax?))
    (gen-case-first-order-checks inits ?rest (gen-case-wraps inits ?rest body)))

  #;(define/contract (gen-case-first-order-checks inits ?rest body)
    ((listof syntax?) (or/c #f syntax?) (listof syntax?) . -> . (listof syntax?))

    (hack:make-available (-o) chain-checks)
    (define check-rest
      (syntax-parse ?rest
        [((~literal listof) c)
         (define multi? #f)
         (define/with-syntax on-each
           #`(λ ([Wᵢ : -W¹])
               #,(let ([gen (gen-first-order-checks #'c #'Wᵢ)])
                   (if (= 1 (length gen))
                       (car gen)
                       (begin
                         (set! multi? #t)
                         #`(list #,@gen))))))
         (if multi?
             #`(append-map on-each #,(-Wᵣ))
             #`(map on-each #,(-Wᵣ)))]
        [_ #''()]))
    (list
     #`(define (on-first-order-checks-passed [#,(-Γ) : -Γ]) #,@body)
     #`(apply
        (chain-checks '#,(-o) #,(-ℓ) #,(-Σ) #,(-$) #,(-⟪ℋ⟫) #,(-⟦k⟧))
        #,(-Γ)
        on-first-order-checks-passed
        #,@(append-map
            (λ (ctc arg-id)
              (gen-first-order-checks ctc arg-id))
            inits
            (take (-Wⁿ) (length inits)))
        #,check-rest)))

  #;(define/contract (gen-first-order-checks c x)
    (syntax? identifier? . -> . (listof syntax?))
    (let go ([c c] [want-pass? #t])
      (syntax-parse c
        ;; First-order
        [o:o (list #``(o (,#,x) #,want-pass?))]
        #;[l:lit
           ]
        #;[_:id ; parametric seal
           ]
        #;[((~literal not/c) c)
           ]
        #;[(o:cmp r:number)
           ]
        ;; Functions
        ;; Ambig-order contracts
        [_
         (list
          #`(error 'gen-check "TODO: ~a" '#,(syntax->datum c)))])))

  #;(define/contract (gen-case-wraps inits ?rest body)
    ((listof syntax?) (or/c #f syntax?) (listof syntax?) . -> . (listof syntax?))
    (list*
     #`(error 'gen-case-wraps "TODO")
     body))

  (define/contract (gen-cases)
    (-> (listof syntax?))

    (define arity-check-cases
      (let go ([sig (-sig)])
        (syntax-parse sig
          [((~literal ->) c ... _)
           (list (gen-clause (syntax->list #'(c ...))
                             (take (-Wⁿ) (syntax-length #'(c ...)))
                             #f
                             #f))]
          [((~literal ->*) (c ...) #:rest r _)
           (list (gen-clause (syntax->list #'(c ...))
                             (take (-Wⁿ) (syntax-length #'(c ...)))
                             #'r
                             (-Wᵣ)))]
          [((~literal case->) clauses ...)
           (for/list ([clause (in-syntax-list #'(clauses ...))])
             (syntax-parse clause
               [((~literal ->) c ... #:rest r _)
                (gen-clause (syntax->list #'(c ...))
                            (take (-Wⁿ) (syntax-length #'(c ...)))
                            #'r
                            (-Wᵣ))]
               [((~literal ->) c ... _)
                (gen-clause (syntax->list #'(c ...))
                            (take (-Wⁿ) (syntax-length #'(c ...)))
                            #f
                            #f)]))]
          [((~literal ∀/c) _ c) (go #'c)])))
    
    (list
     #`(match #,(-Ws)
         #,@arity-check-cases
         [_
          (define blm (-blm (ℓ-src #,(-ℓ)) '#,(-o) (list 'error-msg) (map -W¹-V #,(-Ws)) #,(-ℓ)))
          (#,(-⟦k⟧) blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))])))

  (define/contract (gen-clause dom-inits arg-inits ?dom-rest ?arg-rest)
    ((listof syntax?) (listof identifier?) (or/c #f syntax?) (or/c #f identifier?) . -> . syntax?)
    (hack:make-available (-o) mon*.c∷ ?t@)
    (define/with-syntax (stx-dom-init-checks ...) (map gen-ctc dom-inits))
    (define/with-syntax stx-pat (if ?arg-rest #`(list* #,@arg-inits #,?arg-rest) #`(list #,@arg-inits)))
    (define/with-syntax stx-check-list
      (cond
        [?dom-rest
         (define dom-rest-elem
           (syntax-parse ?dom-rest
             [((~literal listof) c) #'c]
             [_ #'any/c]))
         #`(list* stx-dom-init-checks ...
                  (make-list (length #,?arg-rest) #,(gen-ctc dom-rest-elem)))]
        [else
         #'(list stx-dom-init-checks ...)]))

    #`[stx-pat
       (define t-args (map -W¹-t #,(-Ws)))
       (define ⟦k⟧:gen-range
         #,(gen-range (if ?dom-rest (arity-at-least (length dom-inits)) (length dom-inits))
                      arg-inits
                      ?arg-rest
                      (-⟦k⟧)))
       (define ⟦k⟧:chk-args (mon*.c∷ (-ctx (ℓ-src #,(-ℓ)) '#,(-o) '#,(-o) #,(-ℓ))
                                     stx-check-list
                                     (apply ?t@ '#,(-o) t-args)
                                     ⟦k⟧:gen-range))
       (⟦k⟧:chk-args (-W (map -W¹-V #,(-Ws)) (apply ?t@ 'values t-args)) #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))])

  (define/contract (gen-range dom-arity arg-inits ?arg-rest k)
    ((or/c exact-nonnegative-integer? arity-at-least?) (listof identifier?) (or/c #f identifier?) identifier? . -> . syntax?)
    k
    #;#`(error 'gen-range "TODO: ~a" '#,(syntax-e k)))

  (define/contract (gen-ctc c)
    (syntax? . -> . syntax?)
    (hack:make-available (-o) +⟪α⟫ℓ₀)

    (define/contract ((go* Comb/C base/c) cs)
      (identifier? syntax? . -> . ((listof syntax?) . -> . (values syntax? boolean?)))
      (match cs
        ['() (values base/c #t)]
        [(list c) (values (go c) (c-flat? c))]
        [(cons c cs*)
         (define-values (Cᵣ r-flat?) ((go* Comb/C base/c) cs*))
         (define Cₗ (go c))
         (define flat? (and (c-flat? c) r-flat?))
         (values #`(#,Comb/C #,flat? (+⟪α⟫ℓ₀ #,Cₗ) (+⟪α⟫ℓ₀ #,Cᵣ)) flat?)]))

    (define/contract (go c)
      (syntax? . -> . syntax?)
      (syntax-parse c
        [o:o #''o]
        [l:lit #'(-≡/c l)]
        [((~literal not/c) c*)
         (define V* (go #'c*))
         #`(-Not/C #,(gen-ctc V*))]
        [(o:cmp r:number)
         (syntax-parse #'o
           [(~literal >/c)  #'(->/c r)]
           [(~literal </c)  #'(-</c r)]
           [(~literal >=/c) #'(-≥/c r)]
           [(~literal <=/c) #'(-≤/c r)]
           [(~literal =/c)  #'(-=/c r)])]
        [((~literal ->) c ... d)
         (define Cs (map gen-ctc (syntax->list #'(c ...))))
         (define D  (gen-rng #'d))
         #`(-=> (list #,@Cs) #,D +ℓ₀)]
        [((~literal ->*) (c ...) #:rest r d)
         (define Cs (map gen-ctc (syntax->list #'(c ...))))
         (define R (gen-ctc #'r))
         (define D (gen-rng #'d))
         #`(-=> (-var (list #,@Cs) #,R) #,D +ℓ₀)]
        [((~literal case->) clauses ...)
         (error 'gen-ctc "TODO: nested case->")]
        [((~literal ∀/c) (x ...) c)
         (error 'gen-ctc "TODO: nested ∀/c")]
        [((~literal and/c) c ...)
         (define-values (V _) ((go* #'-And/C #''any/c) (syntax->list #'(c ...))))
         V]
        [((~literal or/c) c ...)
         (define-values (V _) ((go* #'-Or/C #''none/c) (syntax->list #'(c ...))))
         V]
        [((~literal cons/c) c d)
         #`(-St/C #,(and (c-flat? #'c) (c-flat? #'d)) -𝒾-cons (list #,(gen-ctc #'c) #,(gen-ctc #'d)))]
        [((~literal listof) c)
         (error 'gen-ctc "TODO: listof")]
        [((~literal list/c) c ...)
         (go (foldr (λ (c d) #`(cons/c #,c #,d)) #'null? (syntax->list #'(c ...))))]
        [((~literal vectorof) c)
         #`(-Vectorof #,(gen-ctc #'c))]
        [((~literal vector/c) c ...)
         #`(-Vector/C (list #,@(map gen-ctc (syntax->list #'(c ...)))))]
        [((~literal set/c) c)
         (error 'gen-ctc "TODO: set/c")]
        [((~literal hash/c) c)
         (error 'gen-ctc "TODO: hash/c")]
        [_
         #`(error 'gen-ctc "TODO ~a" '#,c)]))
    
    #`(+⟪α⟫ℓ₀ #,(go c)))

  (define/contract gen-rng
    (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc (syntax->list #'(c ...))))]
      [(~literal any) #''any]
      [c #`(list #,(gen-ctc #'c))]))
  )
