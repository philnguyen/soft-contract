#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
;; TODO:
;; - [ ] list/c
;; - [ ] listof
;; - [ ] multiple valued return
;; - [ ] #:other-errors
;; - [ ] limited dependent contract to specify `vector-ref`
;;      , or actually just def/custom it if there are only few cases
(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/splicing
                     syntax/parse
                     "utils.rkt"
                     (only-in "../../utils/pretty.rkt" n-sub))
         racket/match
         racket/set
         syntax/parse/define
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "def-prim-runtime.rkt")

(define alias-table : (HashTable Symbol -o) (make-hasheq))
(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table  : (HashTable Symbol -⟦o⟧!) (make-hasheq))
(define opq-table   : (HashTable Symbol -●) (make-hasheq))
(define debug-table : (HashTable Symbol Any) (make-hasheq))

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

   (define/contract thunks (hash/c symbol? syntax?) (make-hash))

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
              (and* (list #`(⊢?/quick R #,σ-id #,Γ-id -cons? #,W)
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
   (define/contract (gen-sym-case Γ-id)
     (identifier? . -> . (listof syntax?))
     
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
        (list #`(define sₐ (-?@ 'o #,@s-ids))
              #`(set #,@(for/list ([ref (in-list refinement-sets)])
                      #`(-ΓA #,Γ-id (-W (list (-● (set #,@ref))) sₐ)))))]
       [else
        (with-syntax ([refine (format-id #f "refine-~a" (syntax-e #'o))])
          (list #'(define sₐ (-?@ 'o #,@s-ids))
                #`(define refine #,(gen-refine-func Γ-id extra-refinements))
                #`(set #,@(for/list ([ref (in-list refinement-sets)])
                        #`(-ΓA #,Γ-id (-W (list (refine (-● (set #,@ref)))) sₐ))))))]))

   ;; Generate primitve body when all preconds have passed
   (define/contract (gen-ok-case Γ-id)
     (identifier? . -> . (listof syntax?))

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
            (define e₀ (go #'pair?))
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
          (list #'(define A (case (MΓ⊢oW M σ #,Γ-id 'o W ...)
                              [(✓) -True/Vs]
                              [(✗) -False/Vs]
                              [(?) -Bool/Vs]))
                #`{set (-ΓA #,Γ-id (-W A (-?@ 'o s ...)))})]
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
                  #,@(gen-sym-case Γ-id)])]
            [else (gen-sym-case Γ-id)])])))

   ;; Generate other error checks not expressed in main contract
   #;(define (gen-other-error-checks Γ-id)
     (log-error "~a: #:other-errors not implemented for now~n" (syntax-e #'o))
     (gen-ok-case Γ-id))

   ;; Guard primitive body with preconditions
   #;(define (gen-precond-checks Ws Vs ss cs)

     (define/contract (gen-precond-check W V s c gen-body)
       (identifier? identifier? identifier? syntax? procedure? . -> . procedure?)
       (with-syntax ([W W]
                     [s s]
                     [.equal? (prefix-id #'equal? #'o)]
                     [.=  (prefix-id #'=  #'o)]
                     [.<  (prefix-id #'<  #'o)]
                     [.<= (prefix-id #'<= #'o)]
                     [.>  (prefix-id #'>  #'o)]
                     [.>= (prefix-id #'>= #'o)])

         (define/contract (gen-test Γ-id W-id c c-blm pos? gen)
           (identifier? identifier? syntax? syntax? boolean? procedure? . -> . syntax?)
           (syntax-parse c
             [((~literal and/c) c* ...)
              (let go ([Γ-id Γ-id]
                       [cs (syntax->list #'(c* ...))]
                       [pos? pos?])
                (match cs
                  [(list c) (gen-test Γ-id W-id c #`(quote #,c) pos? gen)]
                  [(cons c cs*)
                   (gen-test
                    Γ-id W-id c #`(quote #,c) pos?
                    (λ (Γ-id W-id c-blm pos*?)
                      (cond [(equal? pos*? pos?) (go Γ-id cs* pos?)]
                            [else (gen Γ-id W-id c-blm pos*?)])))]))]
             [((~literal or/c) c* ...)
              ;; FIXME can duplicate code due to non-determinism
              ;; FIXME gives misleading blame for cases like (not/c (or/c number? string?))
              ;; Should factor out `gen`
              (let go ([Γ-id Γ-id]
                       [cs (syntax->list #'(c* ...))]
                       [pos? pos?])
                (match cs
                  [(list c)
                   (gen-test Γ-id W-id c #`(quote #,c) pos? gen)]
                  [(cons c cs*)
                   (gen-test
                    Γ-id W-id c #`(quote #,c) pos?
                    (λ (Γ-id W-id c-blm pos*?)
                      (cond [(equal? pos*? pos?) (gen Γ-id W-id c-blm pos*?)]
                            [else (go Γ-id cs* pos?)])))]))]
             [((~literal not/c) d)
              (gen-test Γ-id W-id #'d #'(-not/c 'd) (not pos?) gen)]

             [((~literal cons/c) c₁ c₂)
              (gen-test
               Γ-id W-id #'cons? #`-cons? pos?
               (λ (Γ-id W-id c-blm pos*?)
                 (cond
                   [(equal? pos*? pos?)
                    ;; TODO generalize this optimization?
                    ;; Probably uneccessary unless there's (and/c any/c any/c)
                    (syntax-parse #'(c₁ c₂)
                      [((~literal any/c) (~literal any/c))
                       (gen Γ-id W-id c-blm pos?)]
                      [((~literal any/c) _)
                       #`(for/union : (℘ -ΓA) ([W₂ (in-set (unchecked-ac σ -cdr #,W-id))])
                           #,(gen-test Γ-id #'W₂ #'c₂ #''c₂ pos? gen))]
                      [(_ (~literal any/c))
                       #`(for/union : (℘ -ΓA) ([W₁ (in-set (unchecked-ac σ -car #,W-id))])
                           #,(gen-test Γ-id #'W₁ #'c₁ #''c₁ pos? gen))]
                      [(_ _)
                       #`(let ([W₁s (unchecked-ac σ -car #,W-id)]
                               [W₂s (unchecked-ac σ -cdr #,W-id)])
                           (for/union : (℘ -ΓA) ([W₁ (in-set W₁s)])
                             #,(gen-test
                                Γ-id #'W₁ #'c₁ #`(quote c₁) pos?
                                (λ (Γ-id W-id c-blm pos*?)
                                  (cond
                                    [(equal? pos*? pos?)
                                     #`(for/union : (℘ -ΓA) ([W₂ (in-set W₂s)])
                                          #,(gen-test Γ-id #'W₂ #'c₂ #''c₂ pos? gen))]
                                    [else (gen Γ-id W-id c-blm pos*?)])))))])]
                   [else (gen Γ-id W-id c-blm pos*?)])))]
             
             [((~literal =/c) x)
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M #,Γ-id '= (list #,W-id (-W¹ bₓ bₓ)))])
                    #:true  #,(gen #'Γ₁ W-id #'(-=/c x) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(-=/c x) (not pos?))))]
             [((~literal >/c) x)
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M #,Γ-id '> (list #,W-id (-W¹ bₓ bₓ)))])
                    #:true  #,(gen #'Γ₁ W-id #'(->/c x) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(->/c x) (not pos?))))]
             [((~literal >=/c) x)
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M #,Γ-id '>= (list #,W-id (-W¹ bₓ bₓ)))])
                    #:true  #,(gen #'Γ₁ W-id #'(-≥/c x) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(-≥/c x) (not pos?))))]
             [((~literal </c) x)
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M #,Γ-id '< (list #,W-id (-W¹ bₓ bₓ)))])
                    #:true  #,(gen #'Γ₁ W-id #'(-</c x) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(-</c x) (not pos?))))]
             [((~literal <=/c) x)
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M #,Γ-id '<= (list #,W-id (-W¹ bₓ bₓ)))])
                    #:true  #,(gen #'Γ₁ W-id #'(-≤/c x) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(-≤/c x) (not pos?))))]
             [x:lit
              #`(let ([bₓ (-b x)])
                  (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ #,Γ-id 'equal? #,W-id (-W¹ bₓ bₓ))])
                    #:true  #,(gen #'Γ₁ W-id #'(-≡/c bₓ) pos?)
                    #:false #,(gen #'Γ₂ W-id #'(-≡/c bₓ) (not pos?))))]
             [(~literal any/c ) (gen Γ-id W-id #''any/c  pos?)]
             [(~literal none/c) (gen Γ-id W-id #''none/c (not pos?))]
             [c:id
              (with-syntax ([p (syntax-parse #'c ;; TODO tmp hack
                                 [(~or (~literal cons?) (~literal pair?)) #'-cons?]
                                 [(~or (~literal box?)) #'-box?]
                                 [p:id #''p])])
                #`(with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ #,Γ-id p #,W-id)])
                    #:true  #,(gen #'Γ₁ W-id c-blm pos?)
                    #:false #,(gen #'Γ₂ W-id c-blm (not pos?))))]))

         (λ (Γ-id)
           (define (gen-ans Γ-id W-id c ok?)
             (cond [ok? (gen-body Γ-id)]
                   [else #`{set (-ΓA #,Γ-id (-blm l 'o (list #,c) (list (-W¹-V #,W-id))))}]))
           (gen-test Γ-id #'W c #`(quote #,c) #t gen-ans))))

     (match* (Ws Vs ss cs)
       [('() '() '() '())
        (if (null? cₑ-list) gen-ok-case gen-other-error-checks)]
       [((cons W Ws*) (cons V Vs*) (cons s ss*) (cons c cs*))
        (gen-precond-check W V s c (gen-precond-checks Ws* Vs* ss* cs*))]))

   (define/contract (gen-ok-thunk!)
     (-> symbol?)
     (define name 'on-ok)
     (cond [(hash-has-key? thunks name) name]
           [else (hash-set! thunks name (gen-ok-case #'Γ))
                 name]))

   (define/contract (gen-precond-checks! Ws cₓ-list)
     ((listof identifier?) (listof syntax?) . -> . (values symbol? syntax?))
     (match* (Ws cₓ-list)
       [('() '())
        (define on-ok (gen-ok-thunk!))
        #`(#,on-ok Γ)]
       [((cons W Ws*) (cons c cs*))
        ]))

   (define/contract (gen-body!)
     (-> syntax?)
     (define-values (_ e) (gen-precond-checks! Ws cₓ-list))
     e)

   (define body-rest (gen-body!))
   (define local-defns ; important to call *after* `(gen-body!)`
     (for/list ([defn (in-list thunks)])
       (match-define (cons f es) defn)
       #`(define (#,f [Γ : -Γ]) #,@es)))

   (define body
     (with-syntax ([arity-req (format-symbol "~a values" n)]
                   [(W ...) (datum->syntax #f W-ids)]
                   [(V ...) (datum->syntax #f V-ids)]
                   [(s ...) (datum->syntax #f s-ids)])
       #`(match Ws
           [(list W ...)
            (match-define (-Σ σ _ M) Σ)
            (match-define (-W¹ V s) W) ...
            #,@local-defns
            #,body-rest]
           [_ {set (-ΓA Γ (-blm l 'o '(arity-req) (map -W¹-V Ws)))}])))

   (with-syntax* ([.o (prefix-id #'o)]
                  [defn #`(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws) #,body)])
     #`(begin
         (: .o : -⟦o⟧!)
         defn
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn))))])

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: get-prim : Symbol → (Option (U -o -b -●)))
(define (get-prim name)
  (cond [(hash-has-key? prim-table name) name]
        [(hash-ref const-table name #f) => values]
        [(hash-ref alias-table name #f) => values]
        [(hash-ref opq-table name #f) => values]
        [else #f]))

(def-prim add1 ((or/c exact-integer? inexact-real?) . -> . number?))

#|
(def-prim add1
  ((or/c exact-integer? inexact-real?) . -> . number?))

current:

(define (.add1 ⟪ℋ⟫ ℓ l Σ Γ Ws)
  (match Ws
    ((list W₀)
     (match-define (-Σ σ _ M) Σ)
     (match-define (-W¹ V₀ s₀) W₀)
     (with-Γ+/-
       (((Γ₁ Γ₂) (MΓ+/-oW M σ Γ 'exact-integer? W₀)))
       #:true
       (let ((sₐ (-?@ 'add1 s₀)))
         (set (-ΓA Γ₁ (-W (list (-● (set 'number?))) sₐ))))
       #:false
       (with-Γ+/-
         (((Γ₁ Γ₂) (MΓ+/-oW M σ Γ₂ 'inexact-real? W₀)))
         #:true
         (let ((sₐ (-?@ 'add1 s₀)))
           (set (-ΓA Γ₁ (-W (list (-● (set 'number?))) sₐ))))
         #:false
         (set (-ΓA Γ₂ (-blm l 'add1 (list 'inexact-real?) (list (-W¹-V W₀))))))))
    (_ (set (-ΓA Γ (-blm l 'add1 '(|1 values|) (map -W¹-V Ws)))))))

desired:

(define (.add1 ⟪ℋ⟫ ℓ l Σ Γ Ws)
  (match Ws
    ((list W₀)
     (match-define (-Σ σ _ M) Σ)
     (match-define (-W¹ V₀ s₀) W₀)

     (: on-0-not-inexact-real? : Prim-Thunk)
     (define (on-0-not-inexact-real? Γ)
       (set (-ΓA Γ (-blm l 'add1 (list 'inexact-real?) (list (-W¹-V W₀))))))

     (: on-0-not-exact-integer? : Prim-Thunk)
     (define (on-0-not-exact-integer? Γ)
       (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ Γ 'inexact-real? W₀)])
         #:true  (on-ok Γ₁)
         #:false (on-0-not-inexact-real? Γ₂)))

     (: on-ok : Prim-Thunk)
     (define (on-ok Γ)
       (define sₐ (-?@ 'add1 s₀))
       (set (-ΓA Γ₁ (-W (list (-● (set 'number?))) sₐ))))

     (with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ Γ 'exact-integer? W₀)])
       #:true  (on-ok Γ₁)
       #:false (on-0-not-exact-integer? Γ₂)))
    (_ (set (-ΓA Γ (-blm l 'add1 '(|1 values|) (map -W¹-V Ws)))))))
|#
