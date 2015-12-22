#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "utils/set.rkt"
 "primitives/utils.rkt"
 "ast/definition.rkt"
 "runtime/val.rkt" "runtime/addr.rkt" "runtime/arity.rkt" "runtime/store.rkt" "runtime/path-inv.rkt"
 "runtime/summ.rkt" "runtime/simp.rkt"
 "proof-relation/main.rkt"
 (for-syntax
  racket/base racket/match racket/syntax syntax/parse racket/contract
  racket/pretty racket/list racket/function racket/contract
  "utils/sexp-stx.rkt" "utils/pretty.rkt" "utils/set.rkt"
  (except-in "primitives/declarations.rkt" implications base?) "primitives/utils.rkt")
 )
(provide δ -●/Vs)

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Struct primitives (e.g. constructors, predicates, accessors, mutators): systematically generated
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.
(: concrete-impl : Symbol → (Option (-M -σ -Γ (Listof -WV) -src-loc → (Values -Δσ -AΓs))))
;; Table for (semi-)concrete implementations
(define (concrete-impl s)
  (define (error-arity [o : Symbol] [expect : Integer] [given : Integer])
    (error 'δ "Invalid arity uncaught for `~a`: expect ~a, given ~a" o expect given))
  
  (with-args s (M σ Γ Ws loc)
    [any/c  (values '() (-AΓ (list -tt) Γ))]
    [none/c (values '() (-AΓ (list -ff) Γ))]
    [and/c
     (match Ws
       [(list (-W V₁ _) (-W V₂ _))
        (define pos (-src-loc-pos loc))
        (define α₁ (-α.and/c-l pos))
        (define α₂ (-α.and/c-r pos))
        (values (list (cons α₁ V₁) (cons α₂ V₂))
                (-AΓ (list (-And/C (and (C-flat? V₁) (C-flat? V₂)) α₁ α₂)) Γ))]
       [Ws (error-arity 'and/c 2 (length Ws))])]
    [or/c
     (match Ws
       [(list (-W V₁ _) (-W V₂ _))
        (define pos (-src-loc-pos loc))
        (define α₁ (-α.or/c-l pos))
        (define α₂ (-α.or/c-r pos))
        (values (list (cons α₁ V₁) (cons α₂ V₂))
                (-AΓ (list (-Or/C (and (C-flat? V₁) (C-flat? V₂)) α₁ α₂)) Γ))]
       [Ws (error-arity 'or/c 2 (length Ws))])]
    [not/c
     (match Ws
       [(list (-W V _))
        (define α (-α.not/c (-src-loc-pos loc)))
        (values (list (cons α V))
                (-AΓ (list (-Not/C α)) Γ))]
       [Ws (error-arity 'not/c 1 (length Ws))])]

    [vector
     (define pos (-src-loc-pos loc))
     (define αs
       (for/list : (Listof -α.idx) ([(W i) (in-indexed Ws)])
         (-α.idx pos i)))
     (define δσ
       (for/list : -Δσ ([α αs] [W Ws])
         (cons α (close-Γ Γ (-W-x W)))))
     (values δσ (-AΓ (list (-Vector αs)) Γ))]
    [vectorof
     (match Ws
       [(list (-W V _))
        (define α (-α.vectorof (-src-loc-pos loc)))
        (values (list (cons α V))
                (-AΓ (list (-Vectorof α)) Γ))]
       [Ws (error-arity 'vectorof 1 (length Ws))])]
    [vector/c
     (define pos (-src-loc-pos loc))
     (define-values (αs δσ)
       (for/lists ([αs : (Listof -α.vector/c)] [δσ : -Δσ])
                  ([(W i) (in-indexed Ws)])
         (match-define (-W V e) W)
         (define α (-α.vector/c (if e e (cons pos i))))
         (values α (cons α V))))
     (values δσ (-AΓ (list (-Vector/C αs)) Γ))]
    
    [values
     (values '() (-AΓ (map (inst -W-x -V) Ws) Γ))]
    
    [void
     (values '() (-AΓ (list (-b (void))) Γ))]
    [arity-includes?
     (match-define (list (-W V_f _) (-W V_n _)) Ws)
     (cond
       [(-procedure-arity V_f) =>
        (λ ([a : Arity])
          (match V_n
            [(-b (? simple-arity? n))
             (define ans (if (arity-includes? a n) -tt -ff))
             (values '() (-AΓ (list ans) Γ))]
            [else (values '() (-AΓ -●/Vs Γ))]))]
       [else (values '() (-AΓ -●/Vs Γ))])]

    [equal?
     (define Vs
       (case (apply MσΓ⊢oW M σ Γ 'equal? Ws)
         [(✓) (list -tt)]
         [(X) (list -ff)]
         [(?) -●/Vs]))
     (values '() (-AΓ Vs Γ))]
    
    [procedure?
     (define Vs
       (case (apply MσΓ⊢oW M σ Γ 'procedure? Ws)
         [(✓) (list -tt)]
         [(X) (list -ff)]
         [(?) -●/Vs]))
     (values '() (-AΓ Vs Γ))]))

(define-syntax (with-args stx)
  (syntax-parse stx
    [(_ s:id (M:id σ:id Γ:id Ws:id loc:id) [t:id e ...] ...)
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
          (λ ([M : -M] [σ : -σ] [Γ : -Γ] [Ws  : (Listof -WV)] [loc : -src-loc])
            e ...)]
         ...
         [else #f])]))



(define -●/Vs : (List -V) (list -●/V))

;; Language definition for `δ` begins here
(begin-for-syntax

  (define/contract M-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract σ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Γ-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract o-id  (parameter/c identifier?) (make-parameter #f))
  (define/contract Ws-id (parameter/c identifier?) (make-parameter #f))
  (define/contract l-id  (parameter/c identifier?) (make-parameter #f))

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
                  [(X) (list -ff)]
                  [else -●/Vs]))
              (values '() (-AΓ Vs #,(Γ-id)))])]
         ; Return case clause for straightforward lifting of other 1st order operators
         [(and (andmap base? doms) (base? rng))
          (define/contract b-syms (listof symbol?)
            (build-list (length doms) (λ (i) (string->symbol (format "e~a" (n-sub i))))))
          (define/contract b-ids (listof identifier?) (map (curry datum->syntax (M-id)) b-syms))
          (define b-pats (for/list ([b-id b-ids]) #`(-W _ (-b #,b-id))))
          (define b-conds (datum->syntax (M-id) (sexp-and (map mk-cond b-syms doms))))

          (define-values (W-pats W-ids e-ids)
            (for/lists (W-pats W-ids e-ids) ([i (length doms)])
              (define W-id (datum->syntax (M-id) (string->symbol (format "W~a" (n-sub i)))))
              (define e-id (datum->syntax (M-id) (string->symbol (format "e~a" (n-sub i)))))
              (values #`(and #,W-id (-W _ #,e-id)) W-id e-id)))
          (define refinement-clauses
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
                 (values '() (-AΓ -●/Vs (Γ+ #,(Γ-id) (-?@ '#,rng-chk (-?@ '#,op #,@e-ids)))))]))

          (list
           #`[(#,op)
              (match #,(Ws-id)
                ; straightforward lifting for concrete operands
                [(list #,@b-pats)
                 (cond
                   [#,b-conds
                    (define ans (-b (#,op #,@b-ids)))
                    (values '() (-AΓ (list ans) #,(Γ-id)))]
                   [else ; spurious
                    (printf "Internal: Incorrect use of `~a` flows to `δ`~n" '#,op)
                    (values '() ∅)])]
                #,(cond
                    [(null? refinement-clauses)
                     #`[_ (values '() (-AΓ -●/Vs #,(Γ-id)))]]
                    [else
                     #`[(list #,@W-pats)
                        (cond
                          #,@refinement-clauses
                          [else (values '() (-AΓ -●/Vs #,(Γ-id)))])]]))])]
         
         ; Just return operator name for complicated cases
         [else (list op)])]

      [dec
       ;(printf "δ: ignore ~a~n" dec)
       '()])))

;; Generate body of `δ`
(define-syntax (gen-δ-body stx)
  (syntax-parse stx
    [(_ M:id σ:id Γ:id o:id Ws:id l:id)
     (define-values (clauses names)
       (parameterize ([M-id #'M]
                      [σ-id #'σ]
                      [Γ-id #'Γ]
                      [o-id #'o]
                      [Ws-id #'Ws]
                      [l-id #'l])
         ;; Accumulate `clauses` for straightforwardly lifted operators
         ;; and `names` for opaque operators
         (for/fold ([clauses '()] [names '()]) ([dec prims])
           (match (generate-general-clauses dec)
             ['() (values clauses names)]
             [(cons x xs)
              (cond [(symbol? x) (values clauses (cons x (append xs names)))]
                    [else        (values (cons x (append xs clauses)) names)])]))))
     (define body-stx
       #`(case o
           #,@clauses
           [else
            (cond
              [(∋ prim-names o)
               (cond
                 [(concrete-impl o) =>
                  (λ ([f : (-M -σ -Γ (Listof -WV) -src-loc → (Values -Δσ -AΓs))])
                    (f M σ Γ Ws l))]
                 [else (values '() (-AΓ -●/Vs Γ))])]
              [else (error 'δ "unhandled: ~a" o)])]))
     ;(printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ : -M -σ -Γ Symbol (Listof -WV) -src-loc → (Values -Δσ -AΓs))
(define (δ M σ Γ o Ws l)
  (gen-δ-body M σ Γ o Ws l))
