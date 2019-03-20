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
         "../execution/signatures.rkt"
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
    [-Σ identifier? #f]
    [-sig syntax? #f]
    [-Vⁿ (listof identifier?) #f]
    [-Vᵣ (or/c #f identifier?) #f]
    [-gen-lift? boolean? #f]
    [-refinements (listof syntax?) '()]
    [-ctc-parameters (listof identifier?) '()]
    [-volatile? boolean? #t]
    )

  ;; Generate cases from signature
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
           (parameterize ([-ctc-parameters (syntax->list #'(x ...))])
             (go #'c))])))
    (hack:make-available (-o) r:err)
    (list
     #`(match #,(-W)
         #,@cases
         [_ (r:err (Err:Arity '#,(-o) (length #,(-W)) #,(-ℓ)))])))

  ;; Generate abstract result from contract.
  ;; For primitives that take and return base values shared between
  ;; object-language and meta-language, also lift concrete case.
  (define/contract (gen-case dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . syntax?)
    (define/with-syntax pats
      (let ([arg-inits (take (-Vⁿ) (length dom-inits))])
        (if ?dom-rst #`(list* #,@arg-inits #,(-Vᵣ)) #`(list #,@arg-inits))))
    (define/with-syntax (body ...)
      (let ([body-general (gen-case-general dom-inits ?dom-rst rngs)])
        (if (and (-gen-lift?) (should-lift? dom-inits ?dom-rst rngs))
            (gen-case-lift dom-inits ?dom-rst rngs body-general)
            body-general)))
    #'[pats body ...])

  ;; Generated lifted concrete op before resorting to `body`
  (define/contract (gen-case-lift dom-inits ?dom-rst rngs body)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) (listof syntax?) . -> . (listof syntax?))
    (hack:make-available (-o) W->bs r:just)

    (define n-inits (length dom-inits))
    
    ;; Generate basic patterns for init arguments
    (define/with-syntax (bᵢ ...) (gen-ids (-W) 'b (length dom-inits)))
    (define/with-syntax bᵣ (format-id (-W) "bᵣ"))
    (define/with-syntax (a ...) (gen-ids (-W) 'a (length rngs)))
    (define/with-syntax (Vᵢ ...)
      (for/list ([c (in-list dom-inits)] [x (in-syntax-list #'(bᵢ ...))])
        (syntax-parse (?flatten-ctc c)
          [(~or () (~literal any/c)) #`{singleton-set (-b #,x)}]
          [(p ...)
           (with-syntax ([(p* ...) (map for-TR (syntax->list #'(p ...)))])
             #`{singleton-set (-b (and #,x (? p*) ...))})])))

    ;; Generate guards for rest argument list
    (define/with-syntax (pat+grd ...)
      (syntax-parse ?dom-rst
        [#f #'((Vᵢ ...))]
        [((~literal listof) c)
         (define/with-syntax pᵣ
           (syntax-parse (?flatten-ctc #'c)
             [(o) (for-TR #'o)]
             [(o ...)
              (define/with-syntax (o* ...) (map for-TR (syntax->list #'(o ...))))
              #'(λ ([x : Base]) (and (o* x) ...))]))
         #'((Vᵢ ... (app W->bs bᵣ)) #:when (and bᵣ (andmap pᵣ bᵣ)))]
        [_ #'((Vᵢ ... (app W->bs bᵣ)) #:when bᵣ)]))
    (define/with-syntax compute-ans
      (if ?dom-rst #`(apply #,(-o) bᵢ ... bᵣ) #`(#,(-o) bᵢ ...)))
    (list
     (if ?dom-rst
         #`(match* (#,@(take (-Vⁿ) n-inits) #,(-Vᵣ))
             [pat+grd ...
              (define-values (a ...) compute-ans)
              (r:just (list {set (-b a)} ...))]
             [(#,@(make-list n-inits #'_) _) #,@body])
         #`(match* #,(take (-Vⁿ) n-inits)
             [pat+grd ...
              (define-values (a ...) compute-ans)
              (r:just (list {set (-b a)} ...))]
             [#,(make-list n-inits #'_) #,@body]))))

  ;; Generate abstract case for primitive
  (define/contract (gen-case-general dom-inits ?dom-rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . (listof syntax?))
    (hack:make-available (-o) exec-prim r:reify r:just)

    ;; Generate domain contracts
    (define/with-syntax (stx-inits ...) (map gen-ctc-V dom-inits))
    (define/with-syntax doms
      (syntax-parse ?dom-rst
        [#f #'(-var (list stx-inits ...) #f)]
        [((~literal listof) c) #`(-var (list stx-inits ...) #,(gen-ctc-V #'c))]
        [_ #`(-var (list stx-inits ...) 'any/c)]))
    
    ;; Collect refinement clauses whose arities are compatible with this case
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
           (with-syntax ([(C ...) (map gen-ctc-V (syntax->list #'(c ...)))]
                         [D (gen-rng-V #'d)])
             #'(list (list C ...) #f D))]
          [((~literal ->*) (c ...) #:rest r d)
           (with-syntax ([(C ...) (map gen-ctc-V (syntax->list #'(c ...)))]
                         [R (syntax-parse #'r
                              [((~literal listof) c) (gen-ctc-V #'c)]
                              [_ #''any/c])]
                         [D (gen-rng-V #'d)])
             #'(list (list C ...) R D))])))

    ;; Generate expression computing range
    (define/with-syntax compute-range
      (match (?flatten-range rngs)
        ['any
         (log-warning "arbitrarily generate 1 value for range `any` in `~a`~n" (syntax-e (-o)))
         #'(list {set (-● ∅)})]
        [#f #'(list {set (-● ∅)})]
        [initial-refinements
         (with-syntax ([((c ...) ...)
                        (for/list ([cs (in-list initial-refinements)])
                          (map o->v cs))])
           #'(list (r:reify {set c ...}) ...))]))
    `(,@(for/list ([x (in-list (-ctc-parameters))])
          (define/with-syntax x.name (format-symbol "~a:~a" (syntax-e (-o)) (syntax-e x)))
          #`(define #,x (Seal/C (α:dyn (β:sealed 'x.name #,(-ℓ)) H₀) (ℓ-src #,(-ℓ)))))
      ,#`(exec-prim #,(-Σ) #,(-ℓ) '#,(-o)
                    #:volatile? #,(-volatile?)
                    #:dom doms
                    #:rng compute-range
                    #:rng-wrap #,(if (?flatten-range rngs)
                                     #'#f
                                     #`(list #,@(map gen-ctc-V rngs)))
                    #:refinements (list refinement-cases ...)
                    #:args #,(-W))))

  ;; Generate flat checks on arguments before executing `body`
  (define/contract (gen-flat-checks doms ?rst body)
    ((listof syntax?) (or/c #f identifier?) (listof syntax?) . -> . (listof syntax?))

    (define/contract (gen-init-1 c x body)
      (identifier? identifier? (listof syntax?) . -> . (listof syntax?))
      (hack:make-available (-o) r:with-split-Σ r:⧺ r:ΔΣ⧺R)
      (list
       #`(r:with-split-Σ #,(-Σ) '#,c (list #,x)
           (λ (#,(-W) ΔΣ) (let-values ([(r es) (let ()
                                                 #,(match body
                                                     [(list e) e]
                                                     [_ #`(begin #,@body)]))])
                            (values (r:ΔΣ⧺R ΔΣ r) es)))
           (λ _ (blm '#,c #,x)))))

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
      (hack:make-available (-o) r:with-split-Σ r:ΔΣ⧺R)
      (if ?rst
          (list
           #`(let go : (Values R (℘ Err)) ([rests : W #,(-Vᵣ)])
               (match rests
                 [(cons V^ rests*)
                  (r:with-split-Σ #,(-Σ) '#,?rst (list V^)
                    (λ (#,(-W) ΔΣ) (let-values ([(r es) (go rests*)])
                                     (values (r:ΔΣ⧺R ΔΣ r) es)))
                    (λ _ (blm '#,?rst V^)))]
                 ['() #,@body])))
          body))
    (hack:make-available (-o) r:err r:blm)
    (cons
     #`(define (blm [ctc : V] [val : V^])
         (define ℓₒ (loc->ℓ (loc '#,(-o) 0 0 '())))
         (r:err (r:blm (ℓ-src #,(-ℓ)) #,(-ℓ) ℓₒ (list {set ctc}) (list val))))
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

  (define/contract (gen-ctc-α C)
    (syntax? . -> . syntax?)
    #`(γ:imm #,(gen-ctc-V C)))

  (define/contract (gen-ctc-V stx)
    (syntax? . -> . syntax?)
    (define/contract ((go* Comb/C base/c) cs)
      (identifier? syntax? . -> . ((listof syntax?) . -> . syntax?))
      (match cs
        ['() base/c]
        [(list c) (gen-ctc-V c)]
        [(cons c cs*)
         (define Cᵣ ((go* Comb/C base/c) cs*))
         #`(#,Comb/C #,(gen-ctc-α c) (γ:imm #,Cᵣ) #,(gen-stx-ℓ c))]))

    (syntax-parse stx
      [o:o (o->v #'o)]
      [α:id
       (cond
         [(findf (λ (x) (eq? (syntax-e x) (syntax-e #'α))) (-ctc-parameters)) => values]
         [else (raise-syntax-error
                (syntax-e (-o))
                (format "don't know what `~a` means" (syntax-e #'α))
                (-sig)
                #'α)])]
      [l:lit #'(-b l)]
      [((~literal not/c) c*)
       #`(Not/C #,(gen-ctc-α #'c*) #,(gen-stx-ℓ #'c*))]
      [(o:cmp r:number)
       (syntax-parse #'o
         [(~literal >/c)  #'(P:> (-b r))]
         [(~literal </c)  #'(P:< (-b r))]
         [(~literal >=/c) #'(P:≥ (-b r))]
         [(~literal <=/c) #'(P:≤ (-b r))]
         [(~literal =/c)  #'(P:= (-b r))])]
      [((~literal -> )  c ...           d) (gen-==> #'(c ...) #f  #'d)]
      [((~literal ->*) (c ...) #:rest r d) (gen-==> #'(c ...) #'r #'d)]
      [((~literal case->) clauses ...)
       (error 'gen-ctc-V "TODO: nested case-> for `~a`" (syntax-e (-o)))]
      [((~literal ∀/c) (x ...) c)
       (hack:make-available (-o))
       (define/with-syntax tag (gensym (format-symbol "~a:∀/c_" (syntax-e (-o)))))
       (define/with-syntax body (ctc->ast #'c))
       (cond
         [(null? (-ctc-parameters))
          ;; TODO make sure no collision
          #`(∀/C '(x ...) body ∅ #,(gen-stx-ℓ stx))]
         [else
          (with-syntax ([(esc ...)
                         (error 'TODO "generalize env")
                         #;(for/fold ([env #'((inst hasheq Symbol α))])
                                   ([(x a) (in-hash (-ctc-parameters))])
                           #`(hash-set #,env '#,x (γ:imm #,a)))])
            ;; TODO make sure no collision
            #`(∀/C '(x ...) body {set esc ...} #,(gen-stx-ℓ stx)))])]
      [((~literal and/c) c ...)
       ((go* #'And/C #''any/c) (syntax->list #'(c ...)))]
      [((~literal or/c) c ...)
       ((go* #'Or/C #''none/c) (syntax->list #'(c ...)))]
      [((~literal cons/c) c d)
       #`(St/C -𝒾-cons
               (list #,(gen-ctc-α #'c) #,(gen-ctc-α #'d))
               #,(gen-stx-ℓ stx))]
      [((~literal listof) c)
       (define/with-syntax C (gen-ctc-V #'c))
       (define/with-syntax ℓ (gen-stx-ℓ #'c))
       (hack:make-available (-o) make-listof make-static-listof)
       (if (null? (-ctc-parameters))
           (with-syntax ([tag (gensym 'listof)])
             #'(make-static-listof 'tag (λ () (values C ℓ))))
           #'(make-listof C ℓ))]
      [((~literal list/c) c ...)
       (gen-ctc-V (foldr (λ (c d) #`(cons/c #,c #,d)) #'null? (syntax->list #'(c ...))))]
      [((~literal vectorof) c)
       #`(Vectof/C #,(gen-ctc-α #'c) #,(gen-stx-ℓ stx))]
      [((~literal vector/c) c ...)
       #`(Vect/C (vector-immutable #,@(map gen-ctc-α (syntax->list #'(c ...))))
                 #,(gen-stx-ℓ stx))]
      [((~literal set/c) c)
       #`(Set/C #,(gen-ctc-α #'c) #,(gen-stx-ℓ stx))]
      [((~literal hash/c) k v)
       #`(Hash/C #,(gen-ctc-α #'k) #,(gen-ctc-α #'v) #,(gen-stx-ℓ stx))]
      [c (error 'gen-ctc-V "unhandled contract form: ~a" (syntax->datum #'c))]))

  (define/contract gen-rng (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc-α (syntax->list #'(c ...))))]
      [(~literal any) #''#f]
      [c #`(list #,(gen-ctc-α #'c))]))

  (define/contract gen-rng-V (syntax? . -> . syntax?)
    (syntax-parser
      [((~literal values) c ...) #`(list #,@(map gen-ctc-V (syntax->list #'(c ...))))]
      [(~literal any) #''#f]
      [c #`(list #,(gen-ctc-V #'c))]))

  ;; Map object-language's contract to meta-language's expression
  (define/contract (ctc->ast c)
    (syntax? . -> . syntax?)
    (define/with-syntax ℓ (gen-stx-ℓ c))
    (syntax-parse c
      [o:o (o->v #'o)]
      [x:id #'(-x 'x ℓ)]
      [l:lit #'(-b l)]
      [((~literal not/c) c) #`(-@ 'not/c (list #,(ctc->ast #'c)) ℓ)]
      [(cmp:cmp n:number) #'(-@ 'cmp (list (-b n)) ℓ)]
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
      [(~and stx ((~literal ∀/c) (x ...) c))
       (define/with-syntax body (ctc->ast #'c))
       #`(-∀/c '(x ...) body #,(gen-stx-ℓ #'stx))]
      [c (error 'ctc->ast "unimplemented: ~a" (syntax->datum #'c))]))

  ;; Based on domain and range, decide if interpreter can lift concrete op
  (define/contract (should-lift? doms ?rst rngs)
    ((listof syntax?) (or/c #f syntax?) (or/c 'any (listof syntax?)) . -> . boolean?)
    (and (andmap liftable-base? doms)
         (?rst . implies . (syntax-parse ?rst
                             [((~literal listof) c) (liftable-base? #'c)]
                             [(~or (~literal list?) (~literal null?)) #t]
                             [_ #f]))
         (and (list? rngs) (andmap liftable-base? rngs))))

  ;; Map object-language's primitive to meta-language's representation
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
      #;#`(ℓ-with-id #,(-ℓ) (list 'src line col 't ...))
      #'(loc->ℓ (loc 'src line col (list 't ...)))))

  (define/contract (gen-==> inits ?rest rngs)
    (syntax? (or/c #f syntax?) syntax? . -> . syntax?)
    (define/with-syntax init-doms
      (let ([inits (syntax->list inits)])
        (with-syntax* ([(dom ...) (map gen-ctc-α inits)]
                       [(x ...) (gen-names inits (-o))]
                       [(ℓₓ ...) (map gen-stx-ℓ inits)])
          #'(list (Dom 'x dom ℓₓ) ...))))
    (define/with-syntax rest-dom
      (if ?rest
           (with-syntax ([c (gen-ctc-α ?rest)]
                         [x (car (gen-names '(1) (-o)))]
                         [ℓₓ (gen-stx-ℓ ?rest)])
             #'(Dom 'x c ℓₓ))
           #'#f))
    (define/with-syntax rng-doms
      (syntax-parse (gen-rng rngs)
        [((~literal quote) #f) #'#f]
        [((~literal list) rng ...)
         (with-syntax ([(x ...) (gen-names (syntax->list #'(rng ...)) (-o))]
                       [ℓₓ (gen-stx-ℓ rngs)])
           #'(list (Dom 'x rng (ℓ-with-id ℓₓ 'x)) ...))]))
    #'(==>i (-var init-doms rest-dom) rng-doms))

  (define/contract (gen-names xs pre)
    (list? identifier? . -> . (listof symbol?))
    (define prefix (format-symbol "_~a_" (syntax-e pre)))
    (map (λ _ (gensym prefix)) xs))
  )
