#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
(provide def-prim def-prims def-prim/custom def-prim/todo
         def-pred def-preds def-pred/todo
         def-const def-opq
         def-alias def-alias-internal
         -⟦o⟧!
         ;; just for debugging
         const-table prim-table alias-table opq-table get-prim
         )

(require (for-syntax racket/base
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/pretty
                     syntax/parse
                     (only-in "../../utils/pretty.rkt" n-sub))
         racket/match
         racket/set
         racket/contract
         syntax/parse/define
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "../../utils/list.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(begin-for-syntax
  
  (define-syntax-class sig
    #:description "restricted function signature"
    (pattern ((~literal ->) _:fc ... ((~literal values) _:fc ...)))
    (pattern ((~literal ->) _:fc ... _:fc)))

  (define-syntax-class fc
    #:description "restricted first-order contract"
    (pattern ((~or (~literal and/c) (~literal or/c)) _:fc _:fc _:fc ...))
    (pattern ((~literal not/c) _:fc))
    (pattern ((~literal cons/c) _:fc _:fc))
    (pattern ((~or (~literal =/c)
                   (~literal >=/c) (~literal >/c)
                   (~literal <=/c) (~literal </c))
              _:real))
    (pattern _:lit)
    (pattern _:id))

  (define-syntax-class lit
    #:description "restricted literals"
    (pattern x:number)
    (pattern x:symbol))

  (define-syntax-class real
    #:description "literal real number"
    (pattern x #:when (real? (syntax-e #'x))))

  (define-syntax-class symbol
    #:description "literal symbol"
    (pattern ((~literal quote) x) #:when (symbol? (syntax-e #'x))))
  
  (define (prefix-id id [src id]) (format-id src ".~a" (syntax-e id)))

  (define tt? (syntax-parser [#t #t] [_ #f]))
  (define ff? (syntax-parser [#f #t] [_ #f]))

  (define not*
    (syntax-parser
      [#t #'#f]
      [#f #'#t]
      [x #'(not x)]))
  
  (define/contract (and* es)
    ((listof syntax?) . -> . syntax?)
    (define cleaned-es
      (append-map (syntax-parser
                    [#t '()]
                    [((~literal and) e ...) (syntax->list #'(e ...))]
                    [e (list #'e)])
                  es))
    (match cleaned-es
      ['() #'#t]
      [(list e) e]
      [(list _ ... (? ff?) _ ...) #'#f]
      [_ #`(and #,@cleaned-es)]))

  (define/contract (or* es)
    ((listof syntax?) . -> . syntax?)
    (define cleaned-es
      (append-map (syntax-parser
                    [#f '()]
                    [((~literal or) e ...) (syntax->list #'(e ...))]
                    [e (list #'e)])
                  es))
    (match cleaned-es
      ['() #'#f]
      [(list e) e]
      [(list _ ... (? tt?) _ ...) #'#t]
      [else #`(or #,@cleaned-es)]))

  (define/contract (rng->refinement rng)
    (syntax? . -> . (listof syntax?))
    (syntax-parse rng
      [((~literal and/c) cᵢ ...)
       (append-map rng->refinement (syntax->list #'(cᵢ ...)))]
      [((~literal or/c) _ ...)
       (raise-syntax-error 'def-prim "or/c in #:refinement clause not supported" rng)]
      [((~literal not/c) d)
       (cond [(identifier? #'d) (list #'(-not/c 'd))]
             [else
              (raise-syntax-error 'def-prim "only identifier can follow not/c in refinement clause" rng)])]
      [((~literal cons/c) _ _)
       (raise-syntax-error
        'def-prim
        (format "~a: cons/c in range not suported for now" (syntax-e #'o))
        rng)]
      [((~literal =/c) x:number) (list #''real? #'(-=/c x))]
      [((~literal >/c) x:number) (list #''real? #'(->/c x))]
      [((~literal >=/c) x:number) (list #''real? #'(-≥/c x))]
      [((~literal </c) x:number) (list #''real? #'(-</c x))]
      [((~literal <=/c) x:number) (list #''real? #'(-≤/c x))]
      [x:lit (list #'(-≡/c (-b x)))]
      [(~literal any/c) '()]
      [(~literal none/c)
       (raise-syntax-error 'def-prim "refinement clause does not accept none/c in range" rng)]
      [c:id (list #''c)]))

  (define base-predicate?
    (syntax-parser
      [(~or (~literal integer?)
            (~literal rational?)
            (~literal real?)
            (~literal number?)
            (~literal zero?)
            (~literal inexact?)
            (~literal inexact-real?)
            (~literal exact-integer?)
            (~literal exact-positive-integer?)
            (~literal exact-nonnegative-integer?)
            (~literal exact-integer?)
            (~literal flonum?)
            (~literal single-flonum?)
            (~literal extflonum?)
            (~literal boolean?)
            (~literal path-string?)
            (~literal string?)
            (~literal symbol?)
            (~literal keyword?)
            (~literal char?)
            (~literal null?)
            (~literal void?)
            (~literal eof-object?)
            #;(~literal vector?)
            (~literal immutable?)
            (~literal positive?)
            (~literal negative?)
            (~literal zero?))
       #t]
      [_ #f]))

  ;; Check if value constrainted by contract definitly fits in the `Base` type in the implementation
  (define range-is-base?
    (syntax-parser
      [((~literal and/c) c ...)
       (ormap range-is-base? (syntax->list #'(c ...)))]
      [((~literal or/c) c ...)
       (andmap range-is-base? (syntax->list #'(c ...)))]
      [((~literal not) _) #|conservative|# #f]
      [((~literal cons/c) _ _) #f]
      [((~or (~literal =/c)
             (~literal >/c) (~literal >=/c)
             (~literal </c) (~literal <=/c))
        _)
       #t]
      [x:lit #t]
      [x:id (base-predicate? #'x)]))
  
  (define skip-base-case-lifting?
    (syntax-parser
      [(~or (~literal set-equal?)
            (~literal set-eq?)
            (~literal set-eqv?))
       #t]
      [_ #f])))

(: ⊢/quick : -σ -Γ -o -W¹ * → -R)
(define (⊢/quick σ Γ o . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (first-R (apply p∋Vs σ o Vs)
           (Γ⊢e Γ (apply -?@ o ss))))

(: ⊢?/quick : -R -σ -Γ -o -W¹ * → Boolean)
(define (⊢?/quick R σ Γ o . Ws) (eq? R (apply ⊢/quick σ Γ o Ws)))

(define-match-expander res-ff (syntax-rules () [(_) (-W (list (-b #f)) _)]))
(define-match-expander res-uk (syntax-rules () [(_) (-W (list (? -●?)) _)]))

(: dispatch-on-results : (℘ -ΓA) (-Γ → (℘ -ΓA)) (-Γ → (℘ -ΓA)) → (℘ -ΓA))
(define (dispatch-on-results reses ok er)
  (for/union : (℘ -ΓA) ([res (in-set reses)])
    (match-define (-ΓA Γ A) res)
    (match A
      [(res-uk) (∪ (ok Γ) (er Γ))]
      [(res-ff) (er Γ)]
      [_ (ok Γ)])))

(define-simple-macro (match-results res [Γ_t:id e₁ ...] [Γ_f:id e₂ ...])
  (dispatch-on-results res (λ (Γ_t) e₁ ...) (λ (Γ_f) e₂ ...)))

(define-type -⟦o⟧! (-⟪ℋ⟫ -ℓ -l -Σ -Γ (Listof -W¹) → (℘ -ΓA)))

(define alias-table : (HashTable Symbol -o) (make-hasheq))
(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table  : (HashTable Symbol -⟦o⟧!) (make-hasheq))
(define opq-table   : (HashTable Symbol -●) (make-hasheq))

(: get-prim : Symbol → (Option (U -o -b -●)))
(define (get-prim name)
  (cond [(hash-has-key? prim-table name) name]
        [(hash-ref const-table name #f) => values]
        [(hash-ref alias-table name #f) => values]
        [(hash-ref opq-table name #f) => values]
        [else #f]))

(define-syntax-parser def-const
  [(_ x:id)
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x (-b x))
         (hash-set-once! const-table 'x .x)))])

(define-syntax-parser def-prim
  [(_ o:id ((~literal ->) cₓ:fc ... cₐ:fc)
      (~optional (~seq #:other-errors [cₑ:fc ...] ...)
                 #:defaults ([(cₑ 2) null]))
      (~optional (~seq #:refinements [(~literal ->) rₓ:fc ... rₐ:fc] ...)
                 #:defaults ([(rₓ 2) null] [(rₐ 1) null])))
   (define cₓ-list (syntax->list #'(cₓ ...)))
   (define cₑ-list (syntax->list #'((cₑ ...) ...)))
   (define n (length cₓ-list))

   ;; Perform quick checks for arity consistency
   (let ()
     (define (check-domain-arity doms)
       (define m (length (syntax->list doms)))
       (unless (equal? n m)
         (raise-syntax-error
          'def-prim
          (format "~a has arity ~a, but get ~a" (syntax-e #'o) n m)
          doms)))
     (for-each check-domain-arity (syntax->list #'((cₑ ...) ...)))
     (for-each check-domain-arity (syntax->list #'((rₓ ...) ...))))

   ;; Generate identifiers for each argument
   (define-values (W-ids V-ids s-ids b-ids wilds)
     (for/lists (W-ids V-ids s-ids b-ids _s) ([i (in-range n)])
       (define ᵢ (n-sub i))
       (values (format-id #f "W~a" ᵢ)
               (format-id #f "V~a" ᵢ)
               (format-id #f "s~a" ᵢ)
               (format-id #f "b~a" ᵢ)
               #'_)))

   ;; Generate function that refines results when more is known about arguments
   (define/contract (gen-refine-func Γ-id refinements)
     (identifier? (listof syntax?) . -> . syntax?)

     (define-values (refine-dom-list refine-rng-list)
       (for/lists (refine-dom-list refine-rng-list)
                  ([refinement (in-list refinements)])
         (syntax-parse refinement
           [((rₓ ...) rₐ) (values (syntax->list #'(rₓ ...)) #'rₐ)])))

     (define ((gen-check-definitely σ-id Γ-id) W c)
       (define (pos?->R pos?) (if pos? #''✓ #''✗))
       (let go ([c c] [pos? #t])
         
         (with-syntax ([R (pos?->R pos?)])
           (syntax-parse c
             [((~literal and/c) c* ...)
              (and* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
             [((~literal or/c ) c* ...)
              (or* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
             [((~literal not/c) d) (go #'d (not pos?))]
             [((~literal cons/c) c₁ c₂)
              (and* (list #`(⊢?quick R #,σ-id #,Γ-id -cons? #,W)
                          (go #'c₁ pos?)
                          (go #'c₂ pos?)))]
             [((~literal =/c ) x) #`(⊢?/quick R #,σ-id #,Γ-id '=  #,W (-W¹ (-b x) (-b x)))]
             [((~literal >/c ) x) #`(⊢?/quick R #,σ-id #,Γ-id '>  #,W (-W¹ (-b x) (-b x)))]
             [((~literal >=/c) x) #`(⊢?/quick R #,σ-id #,Γ-id '>= #,W (-W¹ (-b x) (-b x)))]
             [((~literal </c ) x) #`(⊢?/quick R #,σ-id #,Γ-id '<  #,W (-W¹ (-b x) (-b x)))]
             [((~literal <=/c) x) #`(⊢?/quick R #,σ-id #,Γ-id '<= #,W (-W¹ (-b x) (-b x)))]
             [(~literal any/c) #'#t]
             [(~literal none/c) #'#f]
             [x:lit #'(⊢?/quick R #,σ-id #,Γ-id 'equal? #,W (-W¹ (-b x) (-b x)))]
             [c:id #`(⊢?/quick R #,σ-id #,Γ-id 'c #,W)]))))

     #`(λ ([V : -V])
         (define σ (-Σ-σ Σ))
         #,@(for/list ([doms (in-list refine-dom-list)]
                       [rng  (in-list refine-rng-list)])
              (define preconds (map (gen-check-definitely #'σ Γ-id) W-ids doms))
              #`(when #,(and* preconds)
                  #,@(for/list ([cᵣ (in-list (rng->refinement rng))])
                       #`(set! V (V+ σ V #,cᵣ)))))
         V))

   ;; Generate primitive body for the case where 1+ argument is symbolic
   (define (gen-sym-case Γ-id)
     (define/contract refinement-sets (listof (listof syntax?))
       (let go ([c #'cₐ])
         (syntax-parse c
           [((~literal and/c) c* ...)
            (let go/and/c ([cs (syntax->list #'(c* ...))])
              (match cs
                ['() (list (list))]
                [(cons c cs*)
                 (remove-duplicates
                  (for/list ([ref-set₁ (in-list (go c))]
                             [ref-set₂ (in-list (go/and/c cs*))])
                    (remove-duplicates (append ref-set₁ ref-set₂))))]))]
           [((~literal or/c) cᵢ ...)
            (append-map go (syntax->list #'(cᵢ ...)))]
           [((~literal not/c) d)
            (cond [(identifier? #'d) (list (list #'(-not/c 'd)))]
                  [else (raise-syntax-error
                         'def-prim
                         (format "~a: only identifier can follow not/c in range" #'o)
                         c)])]
           [((~literal cons/c) _ _)
            (raise-syntax-error
             'def-prim
             (format "~a: cons/c in range not supported for now" (syntax-e #'o))
             c)]
           [((~literal =/c) x) (list (list #''real? #'(-=/c x)))]
           [((~literal >/c) x) (list (list #''real? #'(->/c x)))]
           [((~literal >=/c) x) (list (list #''real? #'(-≥/c x)))]
           [((~literal </c) x) (list (list #''real? #'(-</c x)))]
           [((~literal <=/c) x) (list (list #''real? #'(-≤/c x)))]
           [x:lit (list (list #'(-≡/c (-b x))))]
           [(~literal any/c) (list (list))]
           [(~literal none/c) (list)]
           [c:id {list (list #''c)}])))

     (define extra-refinements (syntax->list #'(((rₓ ...) rₐ) ...)))
     
     (cond
       [(null? extra-refinements)
        #`(let ([sₐ (-?@ 'o #,@s-ids)])
            (set #,@(for/list ([ref (in-list refinement-sets)])
                      #`(-ΓA #,Γ-id (-W (list (-● (set #,@ref))) sₐ)))))]
       [else
        (with-syntax ([refine (format-id #f "refine-~a" (syntax-e #'o))])
          #`(let ([sₐ (-?@ 'o #,@s-ids)]
                  [refine #,(gen-refine-func Γ-id extra-refinements)])
              (set #,@(for/list ([ref (in-list refinement-sets)])
                        #`(-ΓA #,Γ-id (-W (list (refine (-● (set #,@ref)))) sₐ))))))]))

   ;; Generate primitve body when all preconds have passed
   (define (gen-ok-case Γ-id)
     (define/contract (gen-base-guard c x)
       (syntax? syntax? . -> . (or/c syntax? #f))
       (let go ([c c])
         (syntax-parse c
           [((~literal and/c) cᵢ ...)
            (define clauses (map go (syntax->list #'(cᵢ ...))))
            (and (andmap values clauses) (and* clauses))]
           [((~literal or/c) cᵢ ...)
            (define clauses (map go (syntax->list #'(cᵢ ...))))
            (and (andmap values clauses) (or* clauses))]
           [((~literal not/c) d)
            (define clause (go #'d))
            (and clause (not* clause))]
           [((~literal cons/c) c₁ c₂)
            (define e₀ (go #'pair? x))
            (define e₁ (and e₀ (gen-base-guard #'c₁ #`(car #,x))))
            (define e₂ (and e₁ (gen-base-guard #'c₂ #`(cdr #,x))))
            (and e₂ (and* (list e₀ e₁ e₂)))]
           [((~or (~literal =/c)
                  (~literal >/c) (~literal >=/c)
                  (~literal </c) (~literal <=/c))
             _)
            #`(real? #,x)]
           [_:number #`(number? #,x)]
           [_:symbol #`(symbol? #,x)]
           [(~literal any/c) #'#t]
           [(~literal none/c) #'#f]
           [(~literal integer?) #`(exact-integer? #,x)]
           [c:id (and (base-predicate? #'c) #`(c #,x))])))
     (define (simp@ f xs)
       (syntax-parse f
         [(~literal any/c) #'-tt]
         [(~literal none/c) #'-ff]
         [_ #`(-b (#,f #,@xs))]))

     (with-syntax ([(W ...) (datum->syntax #f W-ids)]
                   [(s ...) (datum->syntax #f s-ids)]
                   [(b ...) (datum->syntax #f b-ids)]
                   [(w ...) (datum->syntax #f wilds)])
       (syntax-parse #'cₐ ; generate predicates differently
         [(~literal boolean?)
          #`(let ([A (case (⊢/quick (-Σ-σ Σ) #,Γ-id 'o W ...)
                       [(✓) -True/Vs]
                       [(✗) -False/Vs]
                       [(?) -Bool/Vs])])
              {set (-ΓA #,Γ-id (-W A (-?@ 'o s ...)))})]
         [_
          (define base-guards
            (and (not (skip-base-case-lifting? #'o))
                 (let ([clauses (map gen-base-guard (syntax->list #'(cₓ ...)) b-ids)])
                   (and (andmap values clauses) (and* clauses)))))
          (define lift-concrete-case? (and base-guards (range-is-base? #'cₐ)))
          (cond
            [lift-concrete-case?
             #`(match* (s ...)
                 [((-b b) ...) #:when #,base-guards
                  (define bₐ #,(simp@ #'o b-ids))
                  {set (-ΓA #,Γ-id (-W (list bₐ) bₐ))}]
                 [(w ...)
                  #,(gen-sym-case Γ-id)])]
            [else (gen-sym-case Γ-id)])])))

   ;; Generate other error checks not expressed in main contract
   (define (gen-other-error-checks Γ-id)
     (log-error "~a: #:other-errors not implemented for now~n" (syntax-e #'o))
     (gen-ok-case Γ-id))

   ;; Guard primitive body with preconditions
   (define (gen-precond-checks Ws Vs ss cs)

     (define/contract (gen-precond-check W V s c gen-body)
       (identifier? identifier? identifier? syntax? procedure? . -> . procedure?)
       (with-syntax ([W W]
                     [s s]
                     [.equal? (prefix-id #'equal? #'o)]
                     [.= (prefix-id #'= #'o)]
                     [.< (prefix-id #'< #'o)]
                     [.<= (prefix-id #'<= #'o)]
                     [.> (prefix-id #'> #'o)]
                     [.>= (prefix-id #'>= #'o)])

         (define/contract (gen-test Γ-id c c-blm pos? gen)
           (identifier? syntax? syntax? boolean? procedure? . -> . syntax?)
           (syntax-parse c
             [((~literal and/c) c* ...)
              (let go ([Γ-id Γ-id]
                       [cs (syntax->list #'(c* ...))]
                       [pos? pos?])
                (match cs
                  [(list c) (gen-test Γ-id c #`(quote #,c) pos? gen)]
                  [(cons c cs*)
                   (gen-test
                    Γ-id c #`(quote #,c) pos?
                    (λ (Γ-id c-blm pos*?)
                      (cond [(equal? pos*? pos?) (go Γ-id cs* pos?)]
                            [else #`{set (-ΓA #,Γ-id (-blm l 'o (list #,c-blm) (list #,V)))}])))]))]
             [((~literal or/c) c* ...)
              ;; FIXME can duplicate code due to non-determinism
              ;; FIXME gives misleading blame for cases like (not/c (or/c number? string?))
              ;; Should factor out `gen`
              (let go ([Γ-id Γ-id]
                       [cs (syntax->list #'(c* ...))]
                       [pos? pos?])
                (match cs
                  [(list c)
                   (gen-test Γ-id c #`(quote #,c) pos? gen)]
                  [(cons c cs*)
                   (gen-test
                    Γ-id c #`(quote #,c) pos?
                    (λ (Γ-id c-blm pos*?)
                      (cond [(equal? pos*? pos?) (gen Γ-id c-blm pos*?)]
                            [else (go Γ-id cs* pos?)])))]))]
             [((~literal not/c) d)
              (gen-test Γ-id #'d #'(-not/c 'd) (not pos?) gen)]

             ;; Checking of `cons/c` is slightly less precise
             ;; because struct accessors are not atomic operations
             ;; in the presence of struct contracts
             [((~literal cons/c) c₁ c₂)
              (error "TODO")]
             
             [((~literal =/c) x)
              #`(match-results (.= ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(-=/c x) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(-=/c x) (not pos?))])]
             [((~literal >/c) x)
              #`(match-results (.> ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(->/c x) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(->/c x) (not pos?))])]
             [((~literal >=/c) x)
              #`(match-results (.>= ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(-≥/c x) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(-≥/c x) (not pos?))])]
             [((~literal </c) x)
              #`(match-results (.< ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(-</c x) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(-</c x) (not pos?))])]
             [((~literal <=/c) x)
              #`(match-results (.<= ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(-≤/c x) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(-≤/c x) (not pos?))])]
             [x:lit
              #`(match-results (.equal? ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W (-W¹ (-b x) (-b x))))
                               [Γ_t #,(gen #'Γ_t #'(-≡/c (-b x)) pos?)]
                               [Γ_f #,(gen #'Γ_f #'(-≡/c (-b x)) (not pos?))])]
             [(~literal any/c ) (gen Γ-id #''any/c  pos?)]
             [(~literal none/c) (gen Γ-id #''none/c (not pos?))]
             [c:id
              (with-syntax ([.c (prefix-id #'c #'o)])
                #`(match-results (.c ⟪ℋ⟫ ℓ l Σ #,Γ-id (list W))
                                 [Γ_t #,(gen #'Γ_t c-blm pos?)]
                                 [Γ_f #,(gen #'Γ_f c-blm (not pos?))]))]))

         (λ (Γ-id)
           (define (gen-ans Γ-id c ok?)
             (cond [ok? (gen-body Γ-id)]
                   [else #`{set (-ΓA #,Γ-id (-blm l 'o (list #,c) (list #,V)))}]))
           (gen-test Γ-id c #`(quote #,c) #t gen-ans))))

     (match* (Ws Vs ss cs)
       [('() '() '() '())
        (if (null? cₑ-list) gen-ok-case gen-other-error-checks)]
       [((cons W Ws*) (cons V Vs*) (cons s ss*) (cons c cs*))
        (gen-precond-check W V s c (gen-precond-checks Ws* Vs* ss* cs*))]))

   (define (gen-body Γ-id)
     (with-syntax ([arity-req (format-symbol "~a values" n)]
                   [(W ...) (datum->syntax #f W-ids)]
                   [(V ...) (datum->syntax #f V-ids)]
                   [(s ...) (datum->syntax #f s-ids)]
                   [body ((gen-precond-checks W-ids V-ids s-ids cₓ-list) Γ-id)])
       #`(match Ws
           [(list W ...)
            (match-define (-W¹ V s) W) ...
            body]
           [_ {set (-ΓA Γ (-blm l 'o '(arity-req) (map -W¹-V Ws)))}])))

   (with-syntax ([.o (prefix-id #'o)])
     (define o-defn
       #`(begin
           (: .o : -⟦o⟧!)
           (define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
             #,(gen-body #'Γ))
           (hash-set! prim-table 'o .o)))
     ;(pretty-print (syntax->datum o-defn))
     o-defn)])

(define-syntax-parser def-prim/custom
  [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id) e ...)
   (with-syntax ([.o (prefix-id #'o)])
     #'(begin
         (: .o : -⟦o⟧!)
         (define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
           e ...)
         (hash-set! prim-table 'o .o)))])

(define-simple-macro (def-prim/todo x:id clauses ...)
  (def-prim/custom (x ⟪ℋ⟫ ℓ l Σ Γ Ws)
    (error 'x "TODO: ~a" '(clauses ...))))

(define-simple-macro (def-prims (o:id ... (~optional (~seq #:todo o*:id ...)
                                                     #:defaults ([(o* 1) '()])))
                       clauses ...)
  (begin
    (def-prim o clauses ...) ...
    (def-prim/todo o* clauses ...) ...))

(define-simple-macro (def-pred p:id (~optional (dom:fc ...)
                                               #:defaults ([(dom 1) (list #'any/c)])))
  (def-prim p (dom ... . -> . boolean?)))

(define-simple-macro (def-preds (p:id ... (~optional (~seq #:todo q:id ...)
                                                     #:defaults ([(q 1) '()])))
                       rst ...)
  (begin
    (def-pred p rst ...) ...
    (def-pred/todo q rst ...) ...))

(define-simple-macro (def-pred/todo p:id (~optional (dom:fc ...)
                                                    #:defaults ([(dom 1) (list #'any/c)])) ...)
  (def-prim/todo p (dom ... . -> . boolean?)))

(define-syntax-parser def-alias
  [(_ x:id y:id)
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x : (U -● -⟦o⟧! -b -o)
           (let ([err
                  (λ ()
                    (error 'def-alias "~a not defined before ~a" 'y 'x))])
             (cond [(get-prim 'y) =>
                    (λ ([v : (U -o -b -●)])
                      (cond [(symbol? v) (hash-ref prim-table v err)]
                            [else v]))]
                   [else (err)])))
         (cond [(-●? .x) (hash-set-once! opq-table 'x .x)]
               [(-b? .x) (hash-set-once! const-table 'x .x)]
               [(-o? .x) (hash-set-once! alias-table 'x .x)]
               [else (hash-set-once! prim-table 'x .x)])))])

(define-syntax-parser def-alias-internal
  [(_ x:id v:id)
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x v)
         (hash-set-once! alias-table 'x .x)))])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (with-syntax ([(r ...) (datum->syntax #f (rng->refinement #'c))]
                 [.x (prefix-id #'x)])
     #'(begin
         (define x (-● (set r ...)))
         (hash-set-once! opq-table 'x x)))])


