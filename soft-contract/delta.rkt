#lang typed/racket/base
(require
 racket/match racket/set racket/bool racket/math racket/contract
 "utils.rkt" "ast.rkt" "runtime.rkt" "provability.rkt"
 (for-syntax racket/base syntax/parse racket/contract racket/pretty
             racket/list racket/function racket/contract
             "untyped-macros.rkt" "utils.rkt" "prims.rkt")
 )
(provide δ Γ+/-)

(: Γ+/- (∀ (X Y) -M -σ -Γ (-Γ → X) (Pairof (Listof -WV) (-Γ → Y)) *
           → (Values (Option X) (Setof Y))))
;; Refine the environment with sequence of propositions
;; and return (maybe) final sucessful environment
;; along with each possible failure
;; e.g. {} +/- ([num? n₁] [num? n₂]) -->
;;      (values {num? n₁, num? n₂} {{¬ num? n₁}, {num? n₁, ¬ num? n₂}})
(define (Γ+/- M σ Γ mk-ok . filters)
  (define-values (Γ-ok ans-bads)
    (for/fold ([Γ-ok : (Option -Γ) Γ]
               [ans-bads : (Setof Y) ∅])
              ([filt filters])
      (cond
        [Γ-ok
         (match-define (cons prop mk-bad) filt)
         (match-define (cons W-p W-vs) prop)
         (define-values (Γ-ok* Γ-bad*) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
         (define ans-bads*
           (cond [Γ-bad* (set-add ans-bads (mk-bad Γ-bad*))]
                 [else ans-bads]))
         (values Γ-ok* ans-bads*)]
        [else (values #f ans-bads)])))
  (values (and Γ-ok (mk-ok Γ-ok)) ans-bads))

(: Γ+/-AΓ : -M -σ -Γ (-Γ → -AΓ) (Pairof (Listof -WV) (-Γ → -AΓ)) * → -AΓs)
(define (Γ+/-AΓ M σ Γ mk-ok . filters)
  (define-values (ans-ok ans-bads) (apply Γ+/- M σ Γ mk-ok filters))
  (cond [ans-ok (cond [(set-empty? ans-bads) ans-ok]
                      [else (set-add ans-bads ans-ok)])]
        [else ans-bads]))

(define -list• (list '•))

;; Language definition for `δ` begins here
(begin-for-syntax

  (define/contract M-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract σ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Γ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract o-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Ws-id (parameter/c identifier?) (make-parameter #f))
  (define/contract l-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract guard-arity-id (parameter/c identifier?) (make-parameter #f))

  (define/contract (mk-sym name sub)
    (symbol? integer? . -> . identifier?)
    (datum->syntax (M-id) (string->symbol (format "~a~a" name (n-sub sub)))))

  (define/contract (mk-quote id)
    (identifier? . -> . syntax?)
    #`(quote #,(syntax->datum id)))

  (define/hack (convert-syntax stx)
    (datum->syntax #'here (syntax->datum stx)))

  (define-syntax-class ctc₀
    #:description "basic contract"
    (pattern (~or x:id ((~literal not/c) y:id))))

  (define-syntax-class ctc
    #:description "primitive contract"
    (pattern (~or ((~literal and/c) z:ctc₀ ...) x:ctc₀)))
  
  (define-syntax-class sig
    #:description "primitive signature"
    ;; Figure out the right one. FIXME `→` matches *everything*!!
    (pattern (d:ctc ... (~literal →) r:ctc)))

  ;; Split signature into domain and range
  (define (sig->dom/rng sig)
    (syntax? . -> . (values (listof syntax?) syntax?))
    (syntax-parse sig ; FIXME why can't I use `with-syntax`? :(
      [(x:ctc ... (~literal →) y:ctc)
       (values (syntax->list #'(x ...)) #'y)]))

  (define/contract (gen-match-clause row)
    (syntax? . -> . (listof syntax?))

    (syntax-parse row
      ;; Shorthands
      [(#:pred p:id)
       (gen-match-clause #'(p (any/c → boolean?) #:other-errors))]
      [(#:pred p:id (dom:ctc ...))
       (gen-match-clause #'(p (dom ... → boolean?) #:other-errors))]
      [(#:batch (ops:id ...) main:sig refinements:sig ...)
       (append-map
        (λ (op) (gen-match-clause #`(#,op main refinements ...)))
        (syntax->list #'(ops ...)))]
      [(op:id main:sig refinements:sig ...)
       (gen-match-clause #'(op main refinements ... #:other-errors))]
      ;; Generate case
      [(op:id main:sig refinements:sig ... #:other-errors (guards:ctc ...) ...)
       (define-values (main-dom main-rng) (sig->dom/rng #'main))
       (define n (length main-dom))
       (define W-ids (build-list n (curry mk-sym 'W)))
       (define-values (V-ids e-ids)
         (for/lists (V-ids e-ids)
                    ([W-id W-ids] [i (in-naturals)])
           (values (mk-sym 'V i) (mk-sym 'e i))))

       (define/contract (gen-ok)
         (-> syntax?)
         (define p?-ids
           (syntax-parse main-dom
             [(p?:id ...) (syntax->list #'(p? ...))]
             [_ #f]))
         (cond
           [p?-ids
            (define b-ids
              (for/list ([_ e-ids] [i (in-naturals)])
                (mk-sym 'b i)))
            (define wraps
              (for/list ([b-id b-ids] [p?-id p?-ids])
                (syntax-parse p?-id
                  [(~literal any/c) #`(-b #,b-id)]
                  [_ #`(-b (? #,p?-id #,b-id))])))
            (define _s (make-list (length b-ids) #'_))
            (define V-stx
              #`(match* #,e-ids
                  [#,wraps (list (-b (#,(o-id) #,@b-ids)))]
                  [#,_s -list•]))
            #`(let ([Vs #,V-stx])
                (-AΓ Vs #,(Γ-id)))]
           [else #`(-AΓ -list• #,(Γ-id))]))

       (define/contract (gen-guard W-id V-id ctc)
         (identifier? identifier? syntax? . -> . (listof syntax?))
         (syntax-parse ctc
           [(~literal any/c) '()]
           [p:id
            (define qp #`(quote #,(syntax-e #'p)))
            (define φ #`(list (-W #,qp #,qp) #,W-id))
            (define mk-bad
              #`(λ ([Γ-bad : -Γ])
                  (-AΓ (-blm #,(l-id) (quote #,(o-id)) #,qp (list #,V-id)) Γ-bad)))
            (list #`(cons #,φ #,mk-bad))]
           [((~literal and/c) p? ...)
            (append-map (curry gen-guard W-id V-id) (syntax->list #'(p? ...)))]
           [((~literal not/c) p?:id)
            (list #'(error "not/c"))]))

       (define/contract (check-args)
         (-> (listof syntax?))
         (define defs
           (for/list ([W-id W-ids] [V-id V-ids] [e-id e-ids])
             #`(match-define (-W #,V-id #,e-id) #,W-id)))
         (define guards (append-map gen-guard W-ids V-ids main-dom))
         (append
          defs
          (list
           (if (null? guards)
               (gen-ok)
               #`(Γ+/-AΓ #,(M-id) #,(σ-id) #,(Γ-id)
                         (λ ([Γ-ok : -Γ]) #,(parameterize ([Γ-id #'Γ-ok]) (gen-ok)))
                         #,@guards)))))
       
       (define/contract (gen-prim)
         (-> syntax?)
         #`(#,(guard-arity-id) #,W-ids #,@(check-args)))
       
       
       (parameterize ([o-id #'op])
         (list #`[(op) #,(gen-prim)]))])))

;; Generate body of `δ`
(define-syntax (gen-δ-body stx)
  (syntax-parse stx
    [(_ M:id σ:id Γ:id o:id Ws:id l:id guard-arity:id)
     (define clauses
       (parameterize ([M-id #'M]
                      [σ-id #'σ]
                      [Γ-id #'Γ]
                      [o-id #'o]
                      [Ws-id #'Ws]
                      [l-id #'l]
                      [guard-arity-id #'guard-arity])
         (append-map gen-match-clause (syntax->list (convert-syntax prims)))))
     (define res
       #`(case o #,@clauses [else (error 'δ "unhandled: ~a" o)]))
     (printf "Generated:~n~a~n" (pretty (syntax->datum res)))
     res]))

(: δ : -M -σ -Γ -o (Listof -WV) Mon-Party → -AΓs)
(define (δ M σ Γ o Ws l)
  (define-syntax (with-guarded-arity stx)
    (syntax-parse stx
      [(_ (W:id ...) e ...)
       (define n (length (syntax->list #'(W ...))))
       #`(match Ws
           [(list W ...) e ...]
           [_ (-AΓ (-blm l (assert o symbol?) (-=/C #,n) (WVs->Vs Ws)) Γ)])]))
  (gen-δ-body M σ Γ o Ws l with-guarded-arity))

#|
(: δ : -M -σ -Γ -o (Listof -WV) -src-loc → -AΓs)
;; Interpret primitive operations.
;; Return (Widened_Store × P((Result|Error)×Updated_Facts))
(define (δ M σ Γ o Ws loc)
  (match-define (-src-loc l pos) loc)
  
  (: ans-bad : Mon-Party Mon-Party -V -V → (-Γ → -AΓ))
  (define ((ans-bad l+ lo P V) Γ)
    (-AΓ (-blm l+ lo P (list V)) Γ))
  
  (define-syntax-rule (with-guarded-arity n e ...)
    (cond
      [(= n (length Ws)) e ...]
      [else
       (-AΓ (-blm l (show-o o)
                  (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤)
                  (WVs->Vs Ws))
            Γ)]))
  
  
  (match o
    ;; Primitive predicate
    [(? -pred₁?)
     (with-guarded-arity 1
       (define V_a
         (match (apply MσΓ⊢oW M σ Γ o Ws)
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list V_a) Γ))]

    [(? -pred₂?)
     (with-guarded-arity 2
       (define V_a
         (match (apply MσΓ⊢oW M σ Γ o Ws)
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list V_a) Γ))]

    ;; Multiple values
    ['values (-AΓ (map (inst -W-x -V) Ws) Γ)]
    
    ['vector-length
     (with-guarded-arity 1
       (match-define (list (and W (-W V _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ])
                 (match V
                   [(-Vector αs) (-AΓ (list (-b (length αs))) Γ-ok)]
                   [_ (-AΓ (list '•) Γ-ok)]))
               (cons (list (-W 'vector? 'vector?) W)
                     (λ ([Γ-bad : -Γ])
                       (-AΓ (-blm l 'vector-length 'vector? (list V)) Γ-bad)))))]

    ;; Equality
    ['equal?
     (with-guarded-arity 2
       (match-define (list W₁ W₂) Ws)
       (match-define (-W V₁ e₁) W₁)
       (match-define (-W V₂ e₂) W₂)
       (define ans
         (match (or-R (V≡ V₁ V₂) (MσΓ⊢e M σ Γ (-?@ 'equal? e₁ e₂)))
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list ans) Γ))]
    
    

    ;; Ariths
    ['add1
     (with-guarded-arity 1
       (match-define (list (and W (-W V ?e))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W) (ans-bad l 'add1 'number? V))))]

    ['sub1
     (with-guarded-arity 1
       (match-define (list (and W (-W V ?e))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W) (ans-bad l 'sub1 'number? V))))]
    
    ['+
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '+ 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '+ 'number? V₂))))]

    ['-
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '- 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '- 'number? V₂))))]

    ['*
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '* 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '* 'number? V₂))))]

    ))
|#
