#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "utils/main.rkt"
 "primitives/utils.rkt"
 "ast/definition.rkt"
 "runtime/main.rkt"
 "proof-relation/main.rkt"
 (for-syntax
  racket/base
  racket/match
  (except-in racket/syntax format-symbol)
  syntax/parse
  racket/contract
  racket/pretty
  racket/list
  racket/function
  racket/contract
  "utils/main.rkt"
  (except-in "primitives/declarations.rkt" implications base?) "primitives/utils.rkt")
 )
(provide δ)

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Struct primitives (e.g. constructors, predicates, accessors, mutators): systematically generated
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.
;; Result of `δ` needs not be deterministic, because it can return abstract value
;; representing multiple ones, and errors should have been taken care of by
;; contracts. (These are unsafe primitives).
;; Current range of `δ` contains `blm`, which is just a hack for returning spurious result.
;; Also, `δ` needs not refine path condition
(: concrete-impl : Symbol →
                   (Option (-𝒞 -ℓ -M -σ -Γ (Listof -W¹) → (Values -Δσ -A*))))
;; Table for (semi-)concrete implementations
(define (concrete-impl s)
  (define (error-arity [o : Symbol] [expect : Integer] [given : Integer])
    (error 'δ "Invalid arity uncaught for `~a`: expect ~a, given ~a" o expect given))
  
  (with-args s (𝒞 l ℓ M σ Γ Ws)
    [any/c  (values ⊥σ (list -tt))]
    [none/c (values ⊥σ (list -ff))]
    [and/c
     (match Ws
       [(list (-W¹ V₁ _) (-W¹ V₂ _))
        (define α₁ (-α.and/c-l ℓ 𝒞))
        (define α₂ (-α.and/c-r ℓ 𝒞))
        (values (⊔ (⊔ ⊥σ α₁ V₁) α₂ V₂)
                (list (-And/C (and (C-flat? V₁) (C-flat? V₂)) α₁ α₂)))]
       [Ws (error-arity 'and/c 2 (length Ws))])]
    [or/c
     (match Ws
       [(list (-W¹ V₁ _) (-W¹ V₂ _))
        (define α₁ (-α.or/c-l ℓ 𝒞))
        (define α₂ (-α.or/c-r ℓ 𝒞))
        (values (⊔ (⊔ ⊥σ α₁ V₁) α₂ V₂)
                (list (-Or/C (and (C-flat? V₁) (C-flat? V₂)) α₁ α₂)))]
       [Ws (error-arity 'or/c 2 (length Ws))])]
    [not/c
     (match Ws
       [(list (-W¹ V _))
        (define α (-α.not/c ℓ 𝒞))
        (values (⊔ ⊥σ α V) (list (-Not/C α)))]
       [Ws (error-arity 'not/c 1 (length Ws))])]

    [vector
     (define αs
       (for/list : (Listof -α.idx) ([(W i) (in-indexed Ws)])
         (-α.idx ℓ 𝒞 (assert i exact-nonnegative-integer?))))
     (define δσ
       (for/fold ([δσ : -Δσ ⊥σ]) ([α αs] [W Ws])
         (⊔ δσ α (-W¹-V W))))
     (values δσ (list (-Vector αs)))]
    [vectorof
     (match Ws
       [(list (-W¹ V _))
        (define α (-α.vectorof ℓ 𝒞))
        (values (⊔ ⊥σ α V) (list (-Vectorof α)))]
       [Ws (error-arity 'vectorof 1 (length Ws))])]
    [vector/c
     (define-values (αs-rev δσ)
       (for/fold ([αs-rev : (Listof -α.vector/c) '()] [δσ : -Δσ ⊥σ])
                 ([W Ws] [i : Natural (in-naturals)])
         (match-define (-W¹ V s) W)
         (define α (-α.vector/c ℓ 𝒞 i))
         (values (cons α αs-rev) (⊔ δσ α V))))
     (values δσ (list (-Vector/C (reverse αs-rev))))]
    
    [values (values ⊥σ (map -W¹-V Ws))]
    
    [void (values ⊥σ -Void/Vs)]
    [arity-includes?
     (match-define (list (-W¹ V_f _) (-W¹ V_n _)) Ws)
     (cond
       [(V-arity V_f) =>
        (λ ([a : Arity])
          (match V_n
            [(-b (? simple-arity? n))
             (define ans (if (arity-includes? a n) -tt -ff))
             (values ⊥σ (list ans))]
            [else (values ⊥σ -●/Vs)]))]
       [else (values ⊥σ -●/Vs)])]

    [equal?
     (define Vs
       (case (apply MσΓ⊢oW M σ Γ 'equal? Ws)
         [(✓) (list -tt)]
         [(✗) (list -ff)]
         [(?) -●/Vs]))
     (values ⊥σ Vs)]

    [= ; duplicate of `equal?` (args already guarded by contracts)
     (define Vs
       (case (apply MσΓ⊢oW M σ Γ 'equal? Ws)
         [(✓) (list -tt)]
         [(✗) (list -ff)]
         [(?) -●/Vs]))
     (values ⊥σ Vs)]
    
    [procedure?
     (define Vs
       (case (apply MσΓ⊢oW M σ Γ 'procedure? Ws)
         [(✓) (list -tt)]
         [(✗) (list -ff)]
         [(?) -●/Vs]))
     (values ⊥σ Vs)]
    ))

(define-syntax (with-args stx)
  (syntax-parse stx
    [(_ s:id (𝒞:id l:id ℓ:id M:id σ:id Γ:id Ws:id) [t:id e ...] ...)
     (for ([t-id (in-list (syntax->list #'(t ...)))])
       (define t-sym (syntax->datum t-id))
       (unless (∋ prim-names t-sym)
         (raise-syntax-error
          'with-args
          (format "Undeclared primitive `~a`" t-sym)
          #'([t e ...] ...)
          t-id)))
     #`(case s
         [(t)
          (λ ([𝒞 : -𝒞] [ℓ : -ℓ] [M : -M] [σ : -σ] [Γ : -Γ] [Ws  : (Listof -W¹)])
            e ...)]
         ...
         [else #f])]))

;; Language definition for `δ` begins here
(begin-for-syntax
  (define/contract 𝒞-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract ℓ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract M-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract σ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Γ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract o-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Ws-id (parameter/c identifier?) (make-parameter #f))
  

  (define/contract (mk-sym name sub)
    (symbol? integer? . -> . identifier?)
    (format-id (M-id) "~a~a" name (n-sub sub)))

  (define/contract (generate-general-clauses dec)
    (dec? . -> . (or/c (listof syntax?) (listof symbol?)))

    (match dec

      ;; Expand shorthand cases
      [`(#:pred ,p)
       (generate-general-clauses `(,p (any/c . -> . boolean?) #:other-errors))]
      [`(#:pred ,p (,dom ...))
       (generate-general-clauses `(,p (,@dom . -> . boolean?) #:other-errors))]
      [`(#:batch (,ops ...) ,(? ctc? main) ,(? ctc? refinements) ...)
       (append-map
        (λ (op) (generate-general-clauses `(,op ,main ,@refinements #:other-errors)))
        ops)]
      [`(,(? symbol? op) ,(? arr? main) ,(? arr? refinements) ...)
       (generate-general-clauses `(,op ,main ,@refinements #:other-errors))]

      ;; Ignore non-symbol cases
      [(or `(#:struct-cons ,_ ...)
           `(#:struct-pred ,_ ...)
           `(#:struct-acc ,_ ...)
           `(#:struct-mut ,_ ...)
           `(#:alias ,_ ...))
       '()]

      ;; Handle generate case
      [`(,(and (? symbol?) (not (? ignore-for-now?)) op)
          (,doms ... . -> . ,rng) ,(? arr? refinements) ...
         #:other-errors (,guards ...) ...)

       (cond
         ; Return case clause for straightforward lifting of predicates
         [(∋ base-predicates op)
          (list
           #`[(#,op)
              (define Vs
                (case (apply MσΓ⊢oW #,(M-id) #,(σ-id) #,(Γ-id) '#,op #,(Ws-id))
                  [(✓) (list -tt)]
                  [(✗) (list -ff)]
                  [else -●/Vs]))
              (values ⊥σ Vs)])]
         ; Return case clause for straightforward lifting of other 1st order operators
         [(and (andmap base? doms) (base? rng))
          (define/contract b-syms (listof symbol?)
            (build-list (length doms) (λ (i) (string->symbol (format "e~a" (n-sub i))))))
          (define/contract b-ids (listof identifier?) (map (curry datum->syntax (M-id)) b-syms))
          (define b-pats/abs  (for/list ([b-id b-ids]) #`(-W¹ _ (-b #,b-id))))
          (define b-pats/conc (for/list ([b-id b-ids]) #`(-W¹ (-b #,b-id) _)))
          (define b-conds (datum->syntax (M-id) (sexp-and (map mk-cond b-syms doms))))

          (define-values (W-pats W-ids e-ids)
            (for/lists (W-pats W-ids e-ids) ([i (length doms)])
              (define W-id (datum->syntax (M-id) (string->symbol (format "W~a" (n-sub i)))))
              (define e-id (datum->syntax (M-id) (string->symbol (format "e~a" (n-sub i)))))
              (values #`(and #,W-id (-W¹ _ #,e-id)) W-id e-id)))
          #;(define refinement-clauses
            (for/list ([ref refinements])
              (match-define `(,(? symbol? dom-chks) ... . -> . ,(? symbol? rng-chk)) ref)
              (define arg-checks
                (for/list ([dom-chk dom-chks] [W-id W-ids])
                  #`(equal? '✓ (MσΓ⊢oW #,(M-id) #,(σ-id) #,(Γ-id) '#,dom-chk #,W-id))))
              (define precond ; make it a little prettier
                (match arg-checks
                  [(list e) e]
                  [_ #`(and #,@arg-checks)]))
              #`[#,precond
                 (values ⊥σ (-A* (Γ+ #,(Γ-id) (-?@ '#,rng-chk (-?@ '#,op #,@e-ids))) -●/Vs))]))

          #;(define maybe-refine
            (cond
              [(null? refinement-clauses)
               #`[_ (values ⊥σ (-A* #,(Γ-id) -●/Vs))]]
              [else
               #`[(list #,@W-pats)
                  (cond
                    #,@refinement-clauses
                    [else (values ⊥σ (-A* #,(Γ-id) -●/Vs))])]]))

          (define case-lift
            #`(cond
                [#,b-conds
                 (define ans (-b (#,op #,@b-ids)))
                 (values ⊥σ (list ans))]
                [else ; spurious
                 (printf "Internal: Incorrect use of `~a` flows to `δ`~n" '#,op)
                 (values ⊥σ #|HACK, ignored result|# (-blm 'havoc 'Λ (list 'spurious) '()))]))

          (list
           #`[(#,op)
              (match #,(Ws-id)
                ; straightforward lifting for concrete operands
                [(list #,@b-pats/abs) #,case-lift]
                [_ (values ⊥σ -●/Vs)]
                ;#,maybe-refine ; TODO: see if eager refinement is still neccessary
                )])]
         
         ; Just return operator name for complicated cases
         [else (list op)])]

      [dec
       ;(printf "δ: ignore ~a~n" dec)
       '()])))

;; Generate body of `δ`
(define-syntax (gen-δ-body stx)
  (syntax-parse stx
    [(_ 𝒞:id ℓ:id M:id σ:id Γ:id o:id Ws:id)
     (define-values (clauses names)
       (parameterize ([𝒞-id #'𝒞]
                      [ℓ-id #'ℓ]
                      [M-id #'M]
                      [σ-id #'σ]
                      [Γ-id #'Γ]
                      [o-id #'o]
                      [Ws-id #'Ws])
         ;; Accumulate `clauses` for straightforwardly lifted operators
         ;; and `names` for opaque operators
         (for/fold ([clauses '()] [names '()]) ([dec prims])
           (match (generate-general-clauses dec)
             ['() (values clauses names)]
             [(cons x xs)
              (cond [(symbol? x) (values clauses (cons x (append xs names)))]
                    [else        (values (cons x (append xs clauses)) names)])]))))
     (define body-stx
       #`(if (∋ prim-names o)
             (cond
               [(concrete-impl o) =>
                (λ ([f : (-𝒞 -ℓ -M -σ -Γ (Listof -W¹) → (Values -Δσ -A*))])
                  (f 𝒞 ℓ M σ Γ Ws))]
               [else
                (case o
                  #,@clauses
                  [else (values ⊥σ -●/Vs)])])
             (error 'δ "unhandled: ~a" o)))
     ;(printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ : -𝒞 -ℓ -M -σ -Γ Symbol (Listof -W¹) → (Values -Δσ -A*))
(define (δ 𝒞 ℓ M σ Γ o Ws)
  (gen-δ-body 𝒞 ℓ M σ Γ o Ws))


(module+ test
  (require typed/rackunit)
  
  (: check-δ/b : Symbol (Listof Base) Base → Any)
  ;; Test δ's concrete fragment
  (define (check-δ/b o bs bₐ)
    (define Ws (for/list : (Listof -W¹) ([b bs]) (-W¹ (-b b) (-b b))))
    (define-values (δσ Vs) (δ 0 0 ⊥M ⊥σ ⊤Γ o Ws))
    (check-true (list? Vs))
    (check-equal? ((inst length -V) (cast Vs (Listof -V))) 1)
    (match-define (list V) Vs)
    (check-true (-b? V))
    (match-define (-b a) V)
    (check-equal? a bₐ))

  (check-δ/b '+ '(1 2) 3)
  (check-δ/b 'string-length '("") 0)
  (check-δ/b '/ '(4 3) 4/3)
  (check-δ/b 'integer? '(4.0) #t)
  (check-δ/b 'exact-integer? '(4.0) #f))
