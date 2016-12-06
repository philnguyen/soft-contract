#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
(provide def-const def-prim def-prim/custom)

(require (for-syntax racket/base
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     syntax/parse
                     (only-in "../../utils/pretty.rkt" n-sub))
         racket/match
         racket/set
         racket/contract
         syntax/parse/define
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

#|
(def-const true)
(dec-prim boolean? (any/c → boolean?))
(dec-prim any/c (any/c → (not/c not)))
(dec-alias complex? number?)
(dec-prim +
  (number? number? . -> . number?)
  #:other-errors
  [zero? negative?]
  #:refinements
  [exact-positive-integer? exact-positive-integer? . -> . exact-positive-integer?]
  )
(dec-prim /
  (number? (and/c number? (or/c inexact? (not/c zero?))) . -> . number?)
  (#:refine real? real?  . -> . real?))
|#

(begin-for-syntax
  
  (define-syntax-class fc
    #:description "restricted first-order contract"
    (pattern ((~literal and/c) _:fc _:fc _:fc ...))
    (pattern ((~literal  or/c) _:fc _:fc _:fc ...))
    (pattern ((~literal not/c) _:fc))
    (pattern _:id))

  (define-syntax-class sig
    #:description "restricted function signature"
    (pattern ((~literal ->) _:fc ... ((~literal values) _:fc ...)))
    (pattern ((~literal ->) _:fc ... _:fc)))

  (define id-prefix ".")

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
      [else #`(or #,@cleaned-es)])))

(: ⊢/quick : -σ -Γ -o -W¹ -R → Boolean)
(define (⊢/quick σ Γ o W R)
  (match-define (-W¹ V s) W)
  (eq? R (first-R (p∋Vs σ o V) (Γ⊢e Γ (-?@ o s)))))

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

(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table : (HashTable Symbol -⟦o⟧!) (make-hasheq))

(define-syntax def-const
  (syntax-parser
    [(_ x:id)
     (with-syntax ([.x (format-id #'x "~a~a" id-prefix (syntax-e #'x))])
       #'(begin
           (define .x (-b x))
           (hash-set-once! const-table 'x .x)))]))

(define-syntax def-prim
  (syntax-parser
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
         (let go ([c c] [pos? #t])
           (syntax-parse c
             [((~literal and/c) c* ...)
              (and* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
             [((~literal or/c ) c* ...)
              (or* (for/list ([cᵢ (in-list #'(c* ...))]) (go cᵢ pos?)))]
             [((~literal not/c) d) (go #'d (not pos?))]
             [(~literal any/c) #'#t]
             [(~literal none/c) #'#f]
             [c:id
              (with-syntax ([r (if pos? #''✓ #''✗)])
                #`(⊢/quick #,σ-id #,Γ-id 'c #,W r))])))

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
           [(~literal any/c) '()]
           [(~literal none/c)
            (raise-syntax-error 'def-prim "refinement clause does not accept none/c in range" rng)]
           [c:id (list #''c)]))
       
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
         (syntax? identifier? . -> . syntax?)
         (let go ([c c])
           (syntax-parse c
             [((~literal and/c) c₁ _ ...) (go #'c₁)]
             [((~literal or/c) cᵢ ...) (or* (map go (syntax->list #'(cᵢ ...))))]
             [((~literal not/c) d) (not* (go #'d))]
             [(~literal any/c) #'#t]
             [(~literal none/c) #'#f]
             [c:id #`(c #,x)])))
       (define (simp@ f xs)
         (syntax-parse f
           [(~literal any/c) #'-tt]
           [(~literal none/c) #'-ff]
           [_ #`(-b (#,f #,@xs))]))
       (define base-guards (and* (map gen-base-guard (syntax->list #'(cₓ ...)) b-ids)))
       (with-syntax ([(s ...) (datum->syntax #f s-ids)]
                     [(b ...) (datum->syntax #f b-ids)]
                     [(w ...) (datum->syntax #f wilds)])
         #`(match* (s ...)
             [((-b b) ...) #:when #,base-guards
              (define bₐ #,(simp@ #'o b-ids))
              {set (-ΓA #,Γ-id (-W (list bₐ) bₐ))}]
             [(w ...)
              #,(gen-sym-case Γ-id)])))

     ;; Generate other error checks not expressed in main contract
     (define (gen-other-error-checks Γ-id)
       (printf "#:other-errors not implemented for now~n")
       (gen-ok-case Γ-id))

     ;; Guard primitive body with preconditions
     (define (gen-precond-checks Ws Vs ss cs)

       (define/contract (gen-precond-check W V s c gen-body)
         (identifier? identifier? identifier? syntax? procedure? . -> . procedure?)
         (with-syntax ([W W]
                       [s s])

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
                        (cond [(equal? pos*? pos?) (go Γ-id cs*)]
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
               [(~literal any/c ) (gen Γ-id #''any/c  pos?)]
               [(~literal none/c) (gen Γ-id #''none/c (not pos?))]
               [c:id
                (with-syntax ([.c (format-id #'c "~a~a" id-prefix (syntax-e #'c))])
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
     
     (with-syntax ([.o (format-id #'o "~a~a" id-prefix (syntax-e #'o))])
       #`(begin
           (: .o : -⟦o⟧!)
           (define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
             #,(gen-body #'Γ))
           (hash-set! prim-table 'o .o)))]))

(define-simple-macro (def-prim/custom (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id) e ...)
  (begin
    (: o : -⟦o⟧!)
    (define (o ⟪ℋ⟫ ℓ l Σ Γ Ws)
      e ...)
    (hash-set! prim-table 'o o)))

(define-simple-macro (def-pred p:id) (def-prim p (any/c . -> . boolean?)))

(define-simple-macro (def-prims (o:id ...) clauses ...)
  (begin
    (def-prim o clauses ...) ...))

(define π 3.14)

(def-const π)

(def-prim any/c (any/c . -> . (not/c not)))
(def-pred not)
(def-pred boolean?)
(def-pred real?)
(def-pred number?)
(def-pred string?)

#;(def-prim expt
  (number? number? . -> . number?)
  #:other-errors
  (zero? negative?))

(def-prim +
  (number? number? . -> . (or/c number? (not/c string?)))
  #:refinements
  (none/c exact-positive-integer? . -> . exact-positive-integer?)
  (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
  (exact-integer? exact-integer? . -> . exact-integer?)
  (integer? integer? . -> . integer?)
  (real? real? . -> . real?)
  (positive? (not/c negative?) . -> . positive?)
  ((not/c negative?) positive? . -> . positive?)
  (negative? (not/c positive?) . -> . negative?)
  ((not/c positive?) negative? . -> . negative?)
  ((not/c negative?) (not/c negative?) . -> . (not/c negative?))
  ((not/c positive?) (not/c positive?) . -> . (not/c positive?))
  )
