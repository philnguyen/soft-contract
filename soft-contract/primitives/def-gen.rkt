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
         "../utils/patterns.rkt"
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
    [-W identifier? #f]
    [-Φ^ identifier? #f]
    [-Ξ identifier? #f]
    [-Σ identifier? #f]
    [-sig syntax? #f]
    [-Vⁿ (listof identifier?) #f]
    [-Vᵣ (or/c #f identifier?) #f]
    [-gen-lift? boolean? #f]
    [-refinements (listof syntax?) '()]
    [-ctc-parameters (hash/c symbol? identifier?) (hash)]
    [-volatile? boolean? #t]
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
    (define/with-syntax error-msg
      (string->symbol (format "arity ~v" (syntax-parse (-sig)
                                           [sig:hc (attribute sig.arity)]))))
    (hack:make-available (-o) r:blm)
    (list
     #`(match #,(-W)
         #,@cases
         [_ (r:blm #,(-ℓ) '#,(-o) (list 'error-msg) #,(-W))])))

  (define/contract (gen-case dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . syntax?)
    (define body-general (gen-case-general dom-inits ?dom-rst rngs))
    (define/with-syntax (body ...)
      (if (and (should-lift? dom-inits ?dom-rst rngs) (-gen-lift?))
          (gen-case-lift dom-inits ?dom-rst rngs body-general)
          body-general))
    (define arg-inits (take (-Vⁿ) (length dom-inits)))
    #`[#,(if ?dom-rst #`(list* #,@arg-inits #,(-Vᵣ)) #`(list #,@arg-inits))
       body ...])

  (define/contract (gen-case-lift dom-inits ?dom-rst rngs body)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) (listof syntax?) . -> . (listof syntax?))
    (hack:make-available (-o) W->bs r:ret!)

    (define (gen-pat c x)
      (syntax-parse (?flatten-ctc c)
        [(~or () (~literal any/c)) #`(-b #,x)]
        [(p ...)
         (with-syntax ([(p* ...) (map for-TR (syntax->list #'(p ...)))])
           #`(-b (and #,x (? p*) ...)))]))
    (define/with-syntax (bᵢ ...) (gen-ids (-W) 'b (length dom-inits)))
    (define/with-syntax bᵣ (format-id (-W) "bᵣ"))
    (define/with-syntax (a ...) (gen-ids (-W) 'a (length rngs)))
    (define/with-syntax (Vᵢ ...) (map gen-pat dom-inits (syntax->list #'(bᵢ ...))))
    (define/with-syntax (pat+grd ...)
      (syntax-parse ?dom-rst
        [#f #'((list Vᵢ ...))]
        [((~literal listof) c)
         (define/with-syntax pᵣ
           (syntax-parse (?flatten-ctc #'c)
             [(o) (for-TR #'o)]
             [(o ...)
              (define/with-syntax (o* ...) (map for-TR (syntax->list #'(o ...))))
              #'(λ ([x : Base]) (and (o* x) ...))]))
         #'((list* Vᵢ ... (app W->bs bᵣ)) #:when (and bᵣ (andmap pᵣ bᵣ)))]
        [_ #'((list* Vᵢ ... (app W->bs bᵣ)) #:when bᵣ)]))
    (define/with-syntax compute-ans
      (if ?dom-rst #`(apply #,(-o) bᵢ ... bᵣ) #`(#,(-o) bᵢ ...)))
    (list
     #`(match #,(-W)
         [pat+grd ...
          (define-values (a ...) compute-ans)
          {set (r:ret! (R (list (-b a) ...) #,(-Φ^)) #,(-Ξ) #,(-Σ))}]
         [_ #,@body])))

  (define/contract (gen-case-general dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . (listof syntax?))
    (hack:make-available (-o) mk-res exec-prim add-seal)
    (define/with-syntax (stx-init-V ...) (map gen-ctc-V dom-inits))
    (define/with-syntax (stx-init-ℓ ...) (map gen-stx-ℓ dom-inits))
    (define/with-syntax (stx-inits ...) #'((cons stx-init-V stx-init-ℓ) ...))
    (define/with-syntax doms
      (syntax-parse ?dom-rst
        [#f #'(list stx-inits ...)]
        [((~literal listof) c)
         (define/with-syntax num-rests #`(length #,(-Vᵣ)))
         #`(list* stx-inits ...
                  (make-list num-rests (cons #,(gen-ctc-V #'c) #,(gen-stx-ℓ #'c))))]
        [_
         (define/with-syntax num-rests #`(length #,(-Vᵣ)))
         #`(list* stx-inits ...
                  (make-list num-rests (cons #,(gen-ctc-V #'any/c) +ℓ₀)))]))
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
    (define/with-syntax compute-range
      (match (?flatten-range rngs)
        ['any
         (log-warning "arbitrarily generate 1 value for range `any` in `~a`~n" (syntax-e (-o)))
         #`(mk-res #,(-Φ^) (list ∅) '#,(-o) #,(-W))]
        [#f #`(mk-res #,(-Φ^) (list ∅) '#,(-o) #,(-W))]
        [initial-refinements
         (with-syntax ([((c ...) ...)
                        (for/list ([cs (in-list initial-refinements)])
                          (map o->v cs))])
           #`(mk-res #,(-Φ^) (list (set c ...) ...) '#,(-o) #,(-W)))]))
    `(,@(for/list ([x (in-hash-values (-ctc-parameters))])
          (define/with-syntax x.name (format-symbol "~a:~a" (syntax-e (-o)) (syntax-e x)))
          (define/with-syntax φ* (gensym 'φ*))
          #`(define #,x (add-seal #,(-Σ) 'x.name (Ξ:co-ctx #,(-Ξ)) (ℓ-src #,(-ℓ)))))
      ,#`(let-values ([(rng Φ^*) compute-range])
           {set (exec-prim #,(-ℓ) '#,(-o) #,(-Ξ) #,(-Σ)
                           #:volatile? #,(-volatile?)
                           #:dom doms
                           #:rng rng
                           #:rng-wrap #,(if (?flatten-range rngs)
                                            #'#f
                                            #`(list #,@(for/list ([d (in-list rngs)])
                                                         #`(cons #,(gen-ctc-V d) #,(gen-stx-ℓ d)))))
                           #:refinements (list refinement-cases ...)
                           #:args (R #,(-W) Φ^*))})))

  (define/contract (gen-flat-checks doms ?rst body)
    ((listof syntax?) (or/c #f identifier?) (listof syntax?) . -> . (listof syntax?))

    (define/contract (gen-init-1 c x body)
      (identifier? identifier? (listof syntax?) . -> . (listof syntax?))
      (hack:make-available (-o) r:split-results r:with-2-paths/collapse)
      (list
       #`((inst r:with-2-paths/collapse Ξ)
          (λ () (r:split-results #,(-Σ) (R (list #,x) #,(-Φ^)) '#,c))
          (λ (#,(-Φ^)) #,(match body [(list e) e] [_ #`(begin #,@body)]))
          (λ (#,(-Φ^)) (blm '#,c #,x)))))

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
      (hack:make-available (-o) r:split-results r:with-2-paths/collapse)
      (if ?rst
          (list
           #`(define (run-body) : (℘ Ξ) #,@body)
           #`(let go ([rests : W #,(-Vᵣ)])
               (match rests
                 [(cons T^ rests*)
                  ((inst r:with-2-paths/collapse Ξ)
                   (λ () (r:split-results #,(-Σ) (R (list T^) #,(-Φ^)) '#,?rst))
                   (λ (#,(-Φ^)) (go rests*))
                   (λ _ (blm '#,?rst T^)))]
                 ['() (run-body)])))
          body))
    (hack:make-available (-o) r:blm)
    (cons
     #`(define (blm [ctc : V] [val : T^])
         (r:blm #,(-ℓ) '#,(-o) (list {set ctc}) (list val)))
     (gen-inits doms (-Vⁿ))))

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
    (with-syntax ([ℓ (gen-stx-ℓ c)]
                  [V (gen-ctc-V c)])
      #'(αℓ (mk-α (-α:imm V)) ℓ)))

  (define/contract (gen-ctc-V stx)
    (syntax? . -> . syntax?)
    (define/contract ((go* Comb/C base/c) cs)
      (identifier? syntax? . -> . ((listof syntax?) . -> . (values syntax? boolean?)))
      (match cs
        ['() (values base/c #t)]
        [(list c) (values (gen-ctc-V c) (c-flat? c))]
        [(cons c cs*)
         (define-values (Cᵣ r-flat?) ((go* Comb/C base/c) cs*))
         (define Cₗ (gen-ctc-V c))
         (define flat? (and (c-flat? c) r-flat?))
         (define ℓₗ (gen-stx-ℓ c 'left))
         (define ℓᵣ (gen-stx-ℓ c 'right))
         (values #`(#,Comb/C #,flat?
                    (αℓ (mk-α (-α:imm #,Cₗ)) #,ℓₗ)
                    (αℓ (mk-α (-α:imm #,Cᵣ)) #,ℓᵣ)) flat?)]))

    (syntax-parse stx
      [o:o (o->v #'o)]
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
       #`(Not/C #,(gen-ctc #'c*))]
      [(o:cmp r:number)
       (syntax-parse #'o
         [(~literal >/c)  #'(P:> r)]
         [(~literal </c)  #'(P:< r)]
         [(~literal >=/c) #'(P:≥ r)]
         [(~literal <=/c) #'(P:≤ r)]
         [(~literal =/c)  #'(P:≡ r)])]
      [((~literal ->) c ... d)
       (define Cs (map gen-ctc (syntax->list #'(c ...))))
       (define D  (gen-rng #'d))
       #`(==> (-var (list #,@Cs) #f) #,D)]
      [((~literal ->*) (c ...) #:rest r d)
       (define Cs (map gen-ctc (syntax->list #'(c ...))))
       (define R (gen-ctc #'r))
       (define D (gen-rng #'d))
       #`(==> (-var (list #,@Cs) #,R) #,D)]
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
                         #`((inst hasheq Symbol α)
                            #,@(append-map
                                (match-lambda
                                  [(cons x V) (list #`'#,x #`(mk-α (-α:imm #,V)))])
                                (hash->list (-ctc-parameters))))])
            #`(make-∀/c '#,(-o) '(x ...) body ρ))]
         [else
          (with-syntax ([env
                         (for/fold ([env #'(hasheq)])
                                   ([(x a) (in-hash (-ctc-parameters))])
                           #`(ρ+ #,env '#,x (mk-α (-α:imm #,a))))])
            #`(let ([Ρ : Ρ env])
                (make-∀/c '#,(-o) '(x ...) body Ρ)))])]
      [((~literal and/c) c ...)
       (define-values (V _) ((go* #'And/C #''any/c) (syntax->list #'(c ...))))
       V]
      [((~literal or/c) c ...)
       (define-values (V _) ((go* #'Or/C #''none/c) (syntax->list #'(c ...))))
       V]
      [((~literal cons/c) c d)
       #`(St/C #,(and (c-flat? #'c) (c-flat? #'d)) -𝒾-cons (list #,(gen-ctc #'c) #,(gen-ctc #'d)))]
      [((~literal listof) c)
       (define/with-syntax C (gen-ctc-V #'c))
       (define/with-syntax flat? (c-flat? #'c))
       (define/with-syntax ℓ (gen-stx-ℓ #'c))
       (hack:make-available (-o) make-listof make-static-listof)
       (if (hash-empty? (-ctc-parameters))
           (with-syntax ([tag (gensym 'listof)])
             #'(make-static-listof 'tag (λ () (values flat? C ℓ))))
           #'(make-listof flat? C ℓ))]
      [((~literal list/c) c ...)
       (gen-ctc-V (foldr (λ (c d) #`(cons/c #,c #,d)) #'null? (syntax->list #'(c ...))))]
      [((~literal vectorof) c)
       #`(Vectof #,(gen-ctc #'c))]
      [((~literal vector/c) c ...)
       #`(Vect/C (list #,@(map gen-ctc (syntax->list #'(c ...)))))]
      [((~literal set/c) c)
       #`(Set/C #,(gen-ctc #'c))]
      [((~literal hash/c) k v)
       #`(Hash/C #,(gen-ctc #'k) #,(gen-ctc #'v))]
      [c (error 'gen-ctc "unhandled contract form: ~a" (syntax->datum #'c))]))

  (define/contract gen-rng (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc (syntax->list #'(c ...))))]
      [(~literal any) #''#f]
      [c #`(list #,(gen-ctc #'c))]))

  (define/contract gen-rng-V (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc-V (syntax->list #'(c ...))))]
      [(~literal any) #''#f]
      [c #`(list #,(gen-ctc-V #'c))]))

  (define/contract (ctc->ast c)
    (syntax? . -> . syntax?)
    (define/with-syntax ℓ (gen-stx-ℓ c))
    (syntax-parse c
      [o:o (o->v #'o)]
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
       #'(-λ (-var '(x) #f) (-@ 'o (list (-x 'x ℓ)) ℓ))]
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
       #'(--> (-var (list dom ...) #f) rng ℓ)]
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
    (and (andmap liftable-base? doms)
         (?rst . implies . (syntax-parse ?rst
                             [((~literal listof) c) (liftable-base? #'c)]
                             [(~or (~literal list?) (~literal null?)) #t]
                             [_ #f]))
         (and (list? rngs) (andmap liftable-base? rngs))))

  (define/contract o->v (identifier? . -> . syntax?)
    (syntax-parser
      [(~or (~literal pair?) (~literal cons?)) #'-cons?]
      [(~literal box?) #'-box?]
      [o #''o]))

  (define/contract (gen-stx-ℓ s . tags)
    ((syntax?) #:rest (listof symbol?) . ->* . syntax?)
    (with-syntax ([src (string->symbol (path->string (syntax-source s)))]
                  [line (syntax-line s)]
                  [col (syntax-column s)]
                  [(t ...) tags])
      #`(ℓ-with-id #,(-ℓ) (list 'src line col 't ...))
      #;(loc->ℓ (loc 'src line col (list 't ...)))))
  )
