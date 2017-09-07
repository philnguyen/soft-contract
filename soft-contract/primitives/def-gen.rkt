#lang typed/racket/base

(provide (for-syntax (all-defined-out)))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/function
                     racket/bool
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
    [-ctc-parameters (hash/c symbol? identifier?) (hash)]
    )

  (define/contract (gen-cases) (-> (listof syntax?))

    (define (on-case c... ?r a)
      (define cs (syntax->list c...))
      (define/syntax-parse d:d a)
      (gen-case cs ?r (attribute d.values)))

    (define cases
      (let go ([sig (-sig)])
        (syntax-parse sig
          [((~literal ->) c ...             d:d) (list (on-case #'(c ...) #f  #'d))]
          [((~literal ->*) (c ...) #:rest r d:d) (list (on-case #'(c ...) #'r #'d))]
          [((~literal case->) clauses ...)
           (map
            (syntax-parser
              [((~literal ->) c ... #:rest r d:d) (on-case #'(c ...) #'r #'d)]
              [((~literal ->) c ...          d:d) (on-case #'(c ...) #f  #'d)])
            (syntax->list #'(clauses ...)))]
          [((~literal ∀/c) (x ...) c)
           (parameterize ([-ctc-parameters (for/hash ([x (in-syntax-list #'(x ...))])
                                             (values (syntax-e x) x))])
             (go #'c))])))
    
    (list
     #`(match #,(-Ws)
         #,@cases
         [_
          (define blm (-blm (ℓ-src #,(-ℓ)) '#,(-o) (list 'error-msg) (map -W¹-V #,(-Ws)) #,(-ℓ)))
          (#,(-⟦k⟧) blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))])))

  (define/contract (gen-case dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . syntax?)
    (define body-general (gen-case-general dom-inits ?dom-rst rngs))
    (define/with-syntax (body ...)
      (if (and (should-lift? dom-inits ?dom-rst rngs) (-gen-lift?))
          (gen-case-lift dom-inits ?dom-rst rngs body-general)
          body-general))
    (define arg-inits (take (-Wⁿ) (length dom-inits)))
    #`[#,(if ?dom-rst #`(list* #,@arg-inits #,(-Wᵣ)) #`(list #,@arg-inits))
       body ...])

  (define/contract (gen-case-lift dom-inits ?dom-rst rngs body)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) (listof syntax?) . -> . (listof syntax?))
    (hack:make-available (-o) Ws->bs)

    (define (gen-pat-W c x)
      (syntax-parse (?flatten-ctc c)
        [(~or () (~literal any/c)) #`(-W¹ _ (-b #,x))]
        [(p)
         (define/with-syntax p* (for-TR #'p))
         #`(-W¹ _ (-b (? p* #,x)))]
        [(p ...)
         (define/with-syntax (p* ...) (map for-TR (syntax->list #'(p ...))))
         #`(-W¹ _ (-b (and #,x (? p) ...)))]))
    (define/with-syntax (bᵢ ...) (gen-ids (-Ws) 'b (length dom-inits)))
    (define/with-syntax bᵣ (format-id (-Ws) "bᵣ"))
    (define/with-syntax (a ...) (gen-ids (-Ws) 'a (length rngs)))
    (define/with-syntax (bₐ ...) (gen-ids (-Ws) 'bₐ (length rngs)))
    (define/with-syntax (Wᵢ ...) (map gen-pat-W dom-inits (syntax->list #'(bᵢ ...))))
    (define/with-syntax (pat ...)
      (syntax-parse ?dom-rst
        [#f #'((list Wᵢ ...))]
        [((~literal listof) c)
         (define/with-syntax pᵣ
           (syntax-parse (?flatten-ctc #'c)
             [(o) (for-TR #'o)]
             [(o ...)
              (define/with-syntax (o* ...) (map for-TR (syntax->list #'(o ...))))
              #'(λ ([x : Base]) (and (o* x) ...))]))
         #'((list* Wᵢ ... (app Ws->bs bᵣ)) #:when (and bᵣ (andmap pᵣ bᵣ)))]
        [_ #'((list* Wᵢ ... (app Ws->bs bᵣ)) #:when bᵣ)]))
    (define/with-syntax compute-ans
      (if ?dom-rst #`(apply #,(-o) bᵢ ... bᵣ) #`(#,(-o) bᵢ ...)))
    (list
     #`(match #,(-Ws)
         [pat ...
          (define-values (a ...) compute-ans)
          (define-values (bₐ ...) (values (-b a) ...))
          (#,(-⟦k⟧) (-W (list bₐ ...)
                        #,@(case (syntax-length #'(bₐ ...))
                             [(1) #'(bₐ ...)]
                             [else #'((-t.@ 'values (list bₐ ...)))]))
           #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ))]
         [_ #,@body])))

  (define/contract (gen-case-general dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . (listof syntax?))
    (hack:make-available (-o) exec-prim mk-●)
    (define/with-syntax (stx-inits ...) (map gen-ctc-V dom-inits))
    (define/with-syntax doms
      (syntax-parse ?dom-rst
        [#f #'(list stx-inits ...)]
        [((~literal listof) c)
         (define/with-syntax num-rests #`(length #,(-Wᵣ)))
         #`(list* stx-inits ... (make-list num-rests #,(gen-ctc-V #'c)))]
        [_
         (define/with-syntax num-rests #`(length #,(-Wᵣ)))
         #`(list* stx-inits ... (make-list num-rests #,(gen-ctc-V #'any/c)))]))
    (define refinement-compatible?
      (let ([case-arity (if ?dom-rst
                            (arity-at-least (length dom-inits))
                            (length dom-inits))])
        (syntax-parser
          [r:mono-hc (arity-compatible? case-arity (attribute r.arity))])))
    (define/with-syntax (refinement-cases ...)
      (for/list ([ref (in-list (-refinements))] #:when (refinement-compatible? ref))
        (syntax-parse ref
          [((~literal ->) c ... d)
           (define/with-syntax (C ...) (map gen-ctc-V (syntax->list #'(c ...))))
           (define/with-syntax D (gen-rng-V #'d))
           #'(list (list C ...) #f D)]
          [((~literal ->*) (c ...) #:rest r d)
           (define/with-syntax (C ...) (map gen-ctc-V (syntax->list #'(c ...))))
           (define/with-syntax R
             (syntax-parse #'r
               [((~literal listof) c) (gen-ctc-V #'c)]
               [_ #''any/c]))
           (define/with-syntax D (gen-rng-V #'d))
           #`(list (list C ...) R D)])))
    (define/with-syntax (V-rng ...)
      (match (?flatten-range rngs)
        ['any
         (log-warning "arbitrarily generate 1 value for range `any` in `~a`~n" (syntax-e (-o)))
         (list #'(mk-●))]
        [#f (make-list (length rngs) #`(mk-●))]
        [initial-refinements
         (for/list ([cs (in-list initial-refinements)])
           (define/with-syntax (c ...) cs)
           #'(mk-● 'c ...))]))
    `(,@(for/list ([x (in-hash-values (-ctc-parameters))])
          (define/with-syntax x.name (format-symbol "~a:~a" (syntax-e (-o)) (syntax-e x)))
          #`(define #,x (-Seal/C 'x.name #,(-⟪ℋ⟫) (ℓ-src #,(-ℓ)))))
      ,#`(exec-prim #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ) #,(-⟦k⟧)
                    #,(-ℓ) '#,(-o)
                    #:dom doms
                    #:rng (list V-rng ...)
                    #:rng-wrap #,(if (?flatten-range rngs)
                                     #'#f
                                     #`(list #,@(map gen-ctc-V rngs)))
                    #:refinements (list refinement-cases ...)
                    #:args #,(-Ws))))

  (define/contract (gen-flat-checks doms ?rst body)
    ((listof syntax?) (or/c #f identifier?) (listof syntax?) . -> . (listof syntax?))

    (define/contract (gen-init-1 c x body)
      (identifier? identifier? (listof syntax?) . -> . (listof syntax?))
      (hack:make-available (-o) r:Γ⊢oW/handler)
      (list
       #`(r:Γ⊢oW/handler
              (λ () #,@body)
              (λ () (blm '#,c #,x))
              (-Σ-σ #,(-Σ)) #,(-Γ) '#,c #,x)))

    (define/contract gen-inits
      ((listof syntax?) (listof identifier?) . -> . (listof syntax?))
      (match-lambda**
       [((cons dom doms) (cons arg args))
        
        (syntax-parse dom
          [c:id (gen-init-1 #'c arg (gen-inits doms args))]
          [((~literal and/c) c:id ...)
           (syntax-parse #'(c ...)
             [() (gen-inits doms args)]
             [(c) (gen-init-1 #'c arg (gen-inits doms args))]
             [(c c* ...)
              (gen-init-1 #'c arg (gen-inits (cons #'(and/c c* ...) doms) (cons arg args)))])])]
       [('() '()) (gen-rest)]))

    (define/contract (gen-rest) (-> (listof syntax?))
      (hack:make-available (-o) r:Γ⊢oW/handler)
      (if ?rst
          (list
           #`(define (run-body) : (℘ -ς) #,@body)
           #`(let go ([rests : (Listof -W¹) #,(-Wᵣ)])
               (match rests
                 [(cons W rests*)
                  (r:Γ⊢oW/handler
                       (λ () (go rests*))
                       (λ () (blm '#,?rst W))
                       (-Σ-σ #,(-Σ)) #,(-Γ) '#,?rst W)]
                 ['() (run-body)])))
          body))
    (list*
     #`(define (blm [ctc : -V] [val : -W¹]) : (℘ -ς)
         (define bl (-blm (ℓ-src #,(-ℓ)) '#,(-o) (list ctc) (list (-W¹-V val)) #,(-ℓ)))
         (#,(-⟦k⟧) bl #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ)))
     (gen-inits doms (-Wⁿ))))

  ;; See if range needs to go through general contract monitoring
  (define/contract (?flatten-range rngs)
    ((or/c 'any (listof syntax?)) . -> . (or/c #f 'any (listof (listof syntax?))))
    (case rngs
      [(any) 'any]
      [else (define flattens (map ?flatten-ctc rngs))
            (and (andmap values flattens) flattens)]))

  (define/contract ?flatten-ctc
    (syntax? . -> . (or/c #f (listof identifier?)))
    (syntax-parser
      [c:o (list #'c)]
      [((~literal and/c) c:o ...) (syntax->list #'(c ...))]
      [_ #f]))

  (define/contract (gen-ctc c)
    (syntax? . -> . syntax?)
    (hack:make-available (-o) +⟪α⟫ℓ₀)
    #`(+⟪α⟫ℓ₀ #,(gen-ctc-V c)))

  (define/contract (gen-ctc-V c)
    (syntax? . -> . syntax?)
    (hack:make-available (-o) +⟪α⟫ℓ₀)
    (define/contract ((go* Comb/C base/c) cs)
      (identifier? syntax? . -> . ((listof syntax?) . -> . (values syntax? boolean?)))
      (match cs
        ['() (values base/c #t)]
        [(list c) (values (gen-ctc-V c) (c-flat? c))]
        [(cons c cs*)
         (define-values (Cᵣ r-flat?) ((go* Comb/C base/c) cs*))
         (define Cₗ (gen-ctc-V c))
         (define flat? (and (c-flat? c) r-flat?))
         (values #`(#,Comb/C #,flat? (+⟪α⟫ℓ₀ #,Cₗ) (+⟪α⟫ℓ₀ #,Cᵣ)) flat?)]))

    (syntax-parse c
      [o:o #''o]
      [α:id
       (hash-ref
        (-ctc-parameters) (syntax-e #'α)
        (λ () (raise-syntax-error
               (syntax-e (-o))
               (format "don't know what `~a` means" (syntax-e #'α))
               (-sig)
               #'α)))]
      [l:lit #'(-b l)]
      [((~literal not/c) c*)
       #`(-Not/C #,(gen-ctc #'c*))]
      [(o:cmp r:number)
       (syntax-parse #'o
         [(~literal >/c)  #'(->/c r)]
         [(~literal </c)  #'(-</c r)]
         [(~literal >=/c) #'(-≥/c r)]
         [(~literal <=/c) #'(-≤/c r)]
         [(~literal =/c)  #'(-b r)])]
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
       (error 'gen-ctc "TODO: nested case-> for `~a`" (syntax-e (-o)))]
      [((~literal ∀/c) (x ...) c)
       (hack:make-available (-o) make-static-∀/c make-∀/c)
       (define/with-syntax tag (gensym (format-symbol "~a:∀/c_" (syntax-e (-o)))))
       (define/with-syntax body (ctc->ast #'c))
       (case (hash-count (-ctc-parameters))
         [(0)
          (with-syntax ([tag (gensym '∀/c)])
            #`(make-static-∀/c 'tag '#,(-o) '(x ...) (λ () body)))]
         [(1 2 3 4)
          (with-syntax ([ρ
                         #`((inst hasheq Symbol ⟪α⟫)
                            #,@(append-map
                                (match-lambda
                                  [(cons x V) (list #`'#,x #`(-α->⟪α⟫ (-α.imm #,V)))])
                                (hash->list (-ctc-parameters))))])
            #`(make-∀/c '#,(-o) '(x ...) body ρ))]
         [else
          (with-syntax ([env
                         (for/fold ([env #'(hasheq)])
                                   ([(x a) (in-hash (-ctc-parameters))])
                           #`(ρ+ #,env '#,x (-α->⟪α⟫ (-α.imm #,a))))])
            #`(let ([ρ : -ρ env])
                (make-∀/c '#,(-o) '(x ...) body ρ)))])]
      [((~literal and/c) c ...)
       (define-values (V _) ((go* #'-And/C #''any/c) (syntax->list #'(c ...))))
       V]
      [((~literal or/c) c ...)
       (define-values (V _) ((go* #'-Or/C #''none/c) (syntax->list #'(c ...))))
       V]
      [((~literal cons/c) c d)
       #`(-St/C #,(and (c-flat? #'c) (c-flat? #'d)) -𝒾-cons (list #,(gen-ctc #'c) #,(gen-ctc #'d)))]
      [((~literal listof) c)
       (define/with-syntax C (gen-ctc-V #'c))
       (define/with-syntax flat? (c-flat? #'c))
       (hack:make-available (-o) make-listof make-static-listof)
       (if (hash-empty? (-ctc-parameters))
           (with-syntax ([tag (gensym 'listof)])
             #'(make-static-listof 'tag (λ () (values flat? C))))
           #'(make-listof flat? C))]
      [((~literal list/c) c ...)
       (gen-ctc-V (foldr (λ (c d) #`(cons/c #,c #,d)) #'null? (syntax->list #'(c ...))))]
      [((~literal vectorof) c)
       #`(-Vectorof #,(gen-ctc #'c))]
      [((~literal vector/c) c ...)
       #`(-Vector/C (list #,@(map gen-ctc (syntax->list #'(c ...)))))]
      [((~literal set/c) c)
       #`(-Set/C #,(gen-ctc #'c))]
      [((~literal hash/c) k v)
       #`(-Hash/C #,(gen-ctc #'k) #,(gen-ctc #'v))]
      [c (error 'gen-ctc "unhandled contract form: ~a" (syntax->datum #'c))]))

  (define/contract gen-rng (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc (syntax->list #'(c ...))))]
      [(~literal any) #''any]
      [c #`(list #,(gen-ctc #'c))]))

  (define/contract gen-rng-V (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc-V (syntax->list #'(c ...))))]
      [(~literal any) #''any]
      [c #`(list #,(gen-ctc-V #'c))]))

  (define/contract (ctc->ast c)
    (syntax? . -> . syntax?)
    (define/with-syntax ℓ
      (with-syntax ([src (path->string (syntax-source c))]
                    [col (syntax-column c)]
                    [row (syntax-line c)])
        #'(loc->ℓ (loc src col row '()))))
    (syntax-parse c
      [o:o #''o]
      [x:id #'(-x 'x ℓ)]
      [l:lit #'(-b l)]
      [((~literal not/c) c)
       (define/with-syntax e (ctc->ast #'c))
       #'(-@ 'not/c (list e) ℓ)]
      [(cmp:cmp n:number)
       (define/with-syntax x (gensym 'cmp))
       (define/with-syntax o
         (syntax-parse #'cmp
           [(~literal </c) '<]
           [(~literal >/c) '>]
           [(~literal <=/c) '<=]
           [(~literal >=/c) '>=]
           [(~literal =/c) '=/c]))
       #'(-λ '(x) (-@ 'o (list (-x 'x ℓ)) ℓ))]
      [((~and o (~or (~literal or/c)
                     (~literal and/c)
                     (~literal cons/c)
                     (~literal listof)
                     (~literal list/c)
                     (~literal vectorof)
                     (~literal vector/c)
                     (~literal set/c)
                     (~literal hash/c)))
        c ...)
       (define/with-syntax (e ...) (map ctc->ast (syntax->list #'(c ...))))
       #'(-@ 'o (list e ...) ℓ)]
      [((~literal ->) c ... d)
       (define/with-syntax (dom ...) (map ctc->ast (syntax->list #'(c ...))))
       (define/with-syntax rng (ctc->ast #'d))
       #'(--> (list dom ...) rng ℓ)]
      [((~literal ->*) (c ...) #:rest r d)
       (define/with-syntax (dom ...) (map ctc->ast (syntax->list #'(c ...))))
       (define/with-syntax rst (ctc->ast #'r))
       (define/with-syntax rng (ctc->ast #'d))
       #'(--> (-var (list dom ...) rst) rng ℓ)]
      [((~literal case->) clauses ...)
       (define/with-syntax (cases ...)
         (for/list ([clause (in-syntax-list #'(clauses ...))])
           (syntax-parse clause
             [((~literal ->) c ... #:rest r d)
              (error 'ctc->ast "TODO: varargs for case-> in `~a`" (syntax-e (-o)))]
             [((~literal ->) c ... d)
              (define/with-syntax (dom ...) (map ctc->ast (syntax->list #'(dom ...))))
              (define/with-syntax rng (ctc->ast #'d))
              #'(cons (list dom ...) rng)])))
       #'(case-> (list cases ...) ℓ)]
      [((~literal ∀/c) (x ...) c)
       (define/with-syntax body (ctc->ast #'c))
       #'(-∀/c '(x ...) body)]
      [c (error 'ctc->ast "unimplemented: ~a" (syntax->datum #'c))]))

  (define/contract (should-lift? doms ?rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . boolean?)
    (and (andmap base? doms)
         (?rst . implies . (syntax-parse ?rst
                             [((~literal listof) c) (base? #'c)]
                             [(~or (~literal list?) (~literal null?)) #t]
                             [_ #f]))
         (and (list? rngs) (andmap base? rngs))))
  )
