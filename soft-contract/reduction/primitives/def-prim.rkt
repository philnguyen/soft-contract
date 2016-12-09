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
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/pretty
                     syntax/parse
                     "utils.rkt"
                     (only-in "../../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         syntax/parse/define
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "def-prim-runtime.rkt")

(define-syntax-parser def-const
  [(_ x:id)
   (with-syntax ([.x (prefix-id #'x)])
     #'(begin
         (define .x (-b x))
         (hash-set-once! const-table 'x .x)))])

(define-syntax-parser def-prim
  ;; Generate total predicates specially to reduce code duplicate
  [(_ o:id ((~literal ->) c ... (~literal boolean?)))
   #:when (for/and ([c (in-list (syntax->list #'(c ...)))])
            (free-identifier=? c #'any/c))
   (define n (length (syntax->list #'(c ...))))
   (with-syntax ([.o (prefix-id #'o)])
     #`(begin
         (define .o ((total-pred #,n) 'o))
         (hash-set! prim-table 'o .o)))]
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
   (define-values (W-ids V-ids s-ids b-ids)
     (for/lists (W-ids V-ids s-ids b-ids) ([i (in-range n)])
       (define ᵢ (n-sub i))
       (values (format-id #f "W~a" ᵢ)
               (format-id #f "V~a" ᵢ)
               (format-id #f "s~a" ᵢ)
               (format-id #f "b~a" ᵢ))))

   ;; Generate function that refines results when more is known about arguments
   (define/contract (gen-refine-body V refinements)
     (identifier? (listof syntax?) . -> . (listof syntax?))

     (define-values (refine-dom-list refine-rng-list)
       (for/lists (refine-dom-list refine-rng-list)
                  ([refinement (in-list refinements)])
         (syntax-parse refinement
           [((rₓ ...) rₐ) (values (syntax->list #'(rₓ ...)) #'rₐ)])))

     (define (gen-check-definitely W c)
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
              (and* (list #`(⊢?/quick R σ Γ -cons? #,W)
                          (go #'c₁ pos?)
                          (go #'c₂ pos?)))]
             [((~literal =/c ) x) #`(⊢?/quick R σ Γ '=  #,W (-W¹ (-b x) (-b x)))]
             [((~literal >/c ) x) #`(⊢?/quick R σ Γ '>  #,W (-W¹ (-b x) (-b x)))]
             [((~literal >=/c) x) #`(⊢?/quick R σ Γ '>= #,W (-W¹ (-b x) (-b x)))]
             [((~literal </c ) x) #`(⊢?/quick R σ Γ '<  #,W (-W¹ (-b x) (-b x)))]
             [((~literal <=/c) x) #`(⊢?/quick R σ Γ '<= #,W (-W¹ (-b x) (-b x)))]
             [(~literal any/c) #'#t]
             [(~literal none/c) #'#f]
             [x:lit #'(⊢?/quick R σ Γ 'equal? #,W (-W¹ (-b x) (-b x)))]
             [c:id #`(⊢?/quick R σ Γ 'c #,W)]))))

     `(,@(for/list ([doms (in-list refine-dom-list)]
                    [rng  (in-list refine-rng-list)])
           (define preconds (map gen-check-definitely W-ids doms))
           #`(when #,(and* preconds)
               #,@(for/list ([cᵣ (in-list (rng->refinement rng))])
                    #`(set! #,V (V+ σ #,V #,cᵣ)))))
       ,V))

   ;; Generate primitive body for the case where 1+ argument is symbolic
   ;; Free variable `Γ` available as "the" path condition
   (define/contract sym-case-body (listof syntax?)
     (let ()
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
                            #`(-ΓA Γ (-W (list (-● (set #,@ref))) sₐ)))))]
         [else
          (with-syntax ([refine (format-id #f "~a.refine" (syntax-e #'o))])
            (list #`(define sₐ (-?@ 'o #,@s-ids))
                  #`(define (refine [V : -V])
                      #,@(gen-refine-body #'V extra-refinements))
                  #`(set #,@(for/list ([ref (in-list refinement-sets)])
                              #`(-ΓA Γ (-W (list (refine (-● (set #,@ref)))) sₐ))))))])))

   ;; Generate primitve body when all preconds have passed
   ;; Free variable `Γ` available as "the" path condition
   (define/contract ok-case-body (listof syntax?)
     (let ()
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
                     [(b ...) (datum->syntax #f b-ids)])
         (syntax-parse #'cₐ ; generate predicates differently
           [(~literal boolean?)
            (list #'(implement-predicate M σ Γ 'o Ws))]
           [_
            (define base-guards
              (and (not (skip-base-case-lifting? #'o))
                   (let ([clauses (map gen-base-guard (syntax->list #'(cₓ ...)) b-ids)])
                     (and (andmap values clauses) (and* clauses)))))
            (define lift-concrete-case? (and base-guards (range-is-base? #'cₐ)))
            (list
             #`(match* ((-W¹-s W) ...)
                 #,@(cond
                      [lift-concrete-case?
                       (list #`[((-b b) ...) #:when #,base-guards
                                (define bₐ #,(simp@ #'o b-ids))
                                {set (-ΓA Γ (-W (list bₐ) bₐ))}])]
                      [else '()])
                 [(s ...) #,@sym-case-body]))]))))

   ;; Generate precondition check before executing `kont`
   (define/contract (gen-precond-check! W c κ push-thunk!)
     (identifier? syntax? symbol? (symbol? (listof syntax?) . -> . symbol?) . -> . symbol?)

     (define gen-name!
       (let ([i 0]
             [infix (syntax-e W)])
         (λ ([prefix 'chk])
           (begin0 (format-symbol "~a-~a-~a" prefix infix i)
             (set! i (add1 i))))))

     (define-values (local-thunks push-local-thunk!) (new-thunk-table))

     (define/contract (go! W c pos? on-done)
       (identifier?
        syntax?
        boolean?
        (identifier? identifier? syntax? boolean? . -> . syntax?)
        . -> . symbol?)

       (define/contract (gen-comp/c-case x ★ ★/c)
         (syntax? identifier? identifier? . -> . symbol?)
         (with-syntax ([why (if pos? #`(#,★/c #,x) #`(-not/c (#,★/c #,x)))])
           (push-local-thunk!
            (gen-name!)
            (list #'(define bₓ (-b #,x))
                  #`(with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ Γ #,★ #,W (-W¹ bₓ bₓ))])
                      #:true  #,(on-done #'Γ₁ W #'why pos?)
                      #:false #,(on-done #'Γ₂ W #'why (not pos?)))))))

       (syntax-parse c
         [((~literal and/c) c* ... cₙ)
          (foldr
           (λ (c κ)
             (go! W c pos?
                  (λ (Γ W c pos*?)
                    (cond [(equal? pos*? pos?) #`(#,κ #,Γ)]
                          [else (on-done Γ W c pos*?)]))))
           (go! W #'cₙ pos? on-done)
           (syntax->list #'(c* ...)))]
         [((~literal or/c) c* ... cₙ)
          (foldr
           (λ (c κ)
             (go! W c pos?
                  (λ (Γ W c pos*?)
                    (cond [(equal? pos*? pos?) (on-done Γ W c pos?)]
                          [else #`(#,κ #,Γ)]))))
           (go! W #'cₙ pos? on-done)
           (syntax->list #'(c* ...)))]
         [((~literal not/c) c*)
          (go! W #'c* (not pos?) on-done)]
         [((~literal cons/c) c₁ c₂)
          (go! W #'cons? pos? on-done ; FIXME
               #;(λ (Γ W c pos*?)
                (cond ; FIXME this is currently wrong
                  [(equal? pos*? pos?)
                   ;; TODO generalize this optimization?
                   ;; Probably no need unless there's `(and/c any/c any/c)`
                   (with-syntax ([W₁ (format-id #'W "~a.car" (syntax-e #'W))]
                                 [W₂ (format-id #'W "~a.cdr" (syntax-e #'W))])
                     (syntax-parse #'(c₁ c₂)
                       [((~literal any/c) (~literal any/c))
                        (on-done Γ W c pos?)]
                       [((~literal any/c) _)
                        #`(for/union : (℘ -ΓA) ([W₂ (in-set (unchecked-ac σ -cdr #,W))])
                             #,(go! #'W₂ #'c₂ pos? on-done))]
                       [(_ (~literal any/c))
                        #`(for/union : (℘ -ΓA) ([W₂ (in-set (unchecked-ac σ -car #,W))])
                             #,(go! #'W₁ #'c₁ pos? on-done))]
                       [(_ _)
                        #`(let ([W₁s (unchecked-ac σ -car #,W)]
                                [W₂s (unchecked-ac σ -cdr #,W)])
                            (for/union : (℘ -ΓA) ([W₁ (in-set W₁s)])
                              #,(go! #'W₁ #'c₁ pos?
                                    (λ (Γ W c pos*?)
                                      (cond
                                        [(equal? pos*? pos?)
                                         #`(for/union : (℘ -ΓA) ([W₂ (in-set W₂s)])
                                             #,(go! #'W₂ #'c₂ pos? on-done))]
                                        [else (on-done Γ W c pos*?)])))))]))]
                  [else (on-done Γ W c pos*?)])))]
         [((~literal =/c ) x) (gen-comp/c-case #'x #'=  #'=/c)]
         [((~literal </c ) x) (gen-comp/c-case #'x #'<  #'</c)]
         [((~literal <=/c) x) (gen-comp/c-case #'x #'<= #'≤/c)]
         [((~literal >/c ) x) (gen-comp/c-case #'x #'>  #'>/c)]
         [((~literal >=/c) x) (gen-comp/c-case #'x #'>= #'≥/c)]
         [x:lit
          (with-syntax ([why (if pos? #'(-≡/c bₓ) #'(-not/c (-≡/c bₓ)))])
            (push-local-thunk!
             (gen-name!)
             (list #'(define bₓ (-b x))
                   #`(with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ Γ 'equal? #,W (-W¹ bₓ bₓ))])
                       #:true  #,(on-done #'Γ₁ W #'why pos?)
                       #:false #,(on-done #'Γ₂ W #'why (not pos?))))))]
         [(~literal any/c )
          (cond [pos? κ]
                [else (push-local-thunk! (gen-name! 'blm) #`(blm Γ l 'o 'none/c #,W))])]
         [(~literal none/c)
          (cond [pos? (push-local-thunk! (gen-name! 'blm) #`(blm Γ l 'o 'none/c #,W))]
                [else κ])]
         [c:id
          (with-syntax ([p (syntax-parse #'c ;; TODO tmp hack
                             [(~or (~literal cons?) (~literal pair?)) #'-cons?]
                             [(~or (~literal box?)) #'-box?]
                             [p:id #''p])]
                        [why (if pos? #''c #'(-not/c 'c))])
            (push-local-thunk!
             (gen-name!)
             #`(with-Γ+/- ([(Γ₁ Γ₂) (MΓ+/-oW M σ Γ p #,W)])
                 #:true  #,(on-done #'Γ₁ W #'why pos?)
                 #:false #,(on-done #'Γ₂ W #'why (not pos?)))))]))

     (define entry-name
       (go! W c #t
            (λ (Γ W c pos?)
              (cond [pos? #`(#,κ #,Γ)]
                    [else #`(blm #,Γ l 'o #,c #,W)]))))
     (cond [(hash-ref local-thunks entry-name #f) =>
            (λ (entry)
              (define body
                `(,@(for/list ([(f es) (in-hash local-thunks)]
                               #:unless (equal? f entry-name))
                      #`(define (#,f [Γ : -Γ]) #,@es))
                  ,@entry))
              (define name (format-symbol "check-~a" (syntax-e W)))
              (push-thunk! name body))]
           [else κ]))

   ;; Generate the main body and local definitions
   (define-values (entry thunk-defns)
     (let-values ([(thunks push-thunk!) (new-thunk-table)])

       (define/contract (step! W c on-done)
         (identifier? syntax? symbol? . -> . symbol?)
         (gen-precond-check! W c on-done push-thunk!))

       (push-thunk! 'on-args-checked ok-case-body)
       (define entry-name (foldr step! 'on-args-checked W-ids cₓ-list))
       (define entry (hash-ref thunks entry-name))
       (define defns
         (for/list ([(f es) (in-hash thunks)] #:unless (equal? f entry-name))
           #`(define (#,f [Γ : -Γ]) #,@es)))
       
       (values entry defns)))

   (with-syntax* ([.o (prefix-id #'o)]
                  [arity-req (format-symbol "~a values" n)]
                  [(W ...) (datum->syntax #f W-ids)]
                  [defn-o
                    #`(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
                        (match Ws
                          [(list W ...)
                           (match-define (-Σ σ _ M) Σ)
                           #,@thunk-defns
                           #,@entry]
                          [_ {set (-ΓA Γ (-blm l 'o '(arity-req) (map -W¹-V Ws)))}]))])
     ;(pretty-write (syntax->datum #'defn-o))
     #`(begin
         (: .o : -⟦o⟧!)
         defn-o
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))))])

(define-syntax-parser def-prim/custom
  [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id) e ...)
   (with-syntax ([.o (prefix-id #'o)])
     #'(begin
         (: .o : -⟦o⟧!)
         (define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
           e ...)
         (hash-set! prim-table 'o .o)))])

(define-simple-macro (def-prim/todo x:id clauses ...)
  (splicing-local ((define already-print? : Boolean #f))
    (def-prim/custom (x ⟪ℋ⟫ ℓ l Σ Γ Ws)
      (unless already-print?
        (set! already-print? #t)
        (log-error "TODO: specify/implement `~a`. Returning ● with no pre-condition check for now~n" 'x))
      (define ss (map -W¹-s Ws))
      {set (-ΓA Γ (-W -●/Vs (apply -?@ 'x ss)))})))

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
                    (error 'def-alias "`~a` not defined before `~a`" 'y 'x))])
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

(define-syntax-parser dec-implications
  [(_ [p:id (~literal ⇒) q:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (with-syntax ([(p ⇒ q ...) clause])
          (for/list ([q (in-list (syntax->list #'(q ...)))])
            #`(add-implication! 'p '#,q))))
      (syntax->list #'([p ⇒ q ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-exclusions
  [(_ [p:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define ps (syntax->list clause))
        (let go ([ps ps] [acc '()])
          (match ps
            [(list) acc]
            [(cons p ps*)
             (go ps*
                 (foldr (λ (p* acc) (cons #`(add-exclusion! '#,p '#,p*) acc)) acc ps*))])))
      (syntax->list #'([p ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-partitions
  [(_ [p:id (q:id ...)] ...)
   (define impl-clauses
     (append-map
      (λ (clause)
        (with-syntax ([(p (q ...)) clause])
          (for/list ([q (in-list (syntax->list #'(q ...)))])
            #`(dec-implications [#,q ⇒ p]))))
      (syntax->list #'([p (q ...)] ...))))
   #`(begin
       (dec-exclusions (q ...) ...)
       #,@impl-clauses)])
