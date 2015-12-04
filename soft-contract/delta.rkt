#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "utils.rkt" "ast.rkt" "prim-gen.rkt" "runtime.rkt" "provability.rkt"
 (for-syntax
  racket/base racket/match racket/syntax syntax/parse racket/contract
  racket/pretty racket/list racket/function racket/contract
  "untyped-utils.rkt" "utils.rkt" (except-in "prims.rkt" implications) "prim-gen.rkt")
 )
(provide δ Γ+/- -●/Vs)

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
       (for/lists ([αs : (Listof -α)] [δσ : -Δσ])
                  ([(W i) (in-indexed Ws)])
         (define V (-W-x W))
         (define α (-α.vector/c pos i))
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
        (λ ([a : -Arity])
          (match V_n
            [(-b (? exact-integer? n))
             (define ans (if (-arity-includes? a n) -tt -ff))
             (values '() (-AΓ (list ans) Γ))]
            [else (values '() (-AΓ -●/Vs Γ))]))]
       [else (values '() (-AΓ -●/Vs Γ))])]))

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

(: Γ+/- (∀ (X Y) -M -σ -Γ (-Γ → X)
           (U (List -WV (Listof -WV) (-Γ → Y))
              (List 'not -WV (Listof -WV) (-Γ → Y))) *
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
         (define-values (Γ-ok* Γ-bad* mk-bad)
           (match filt
             [(list W-p W-vs mk-bad)
              (define-values (Γ-sat Γ-unsat) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
              (values Γ-sat Γ-unsat mk-bad)]
             [(list 'not W-p W-vs mk-bad)
              (define-values (Γ-sat Γ-unsat) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
              (values Γ-unsat Γ-sat mk-bad)]))
         (define ans-bads*
           (cond [Γ-bad* (set-add ans-bads (mk-bad Γ-bad*))]
                 [else ans-bads]))
         (values Γ-ok* ans-bads*)]
        [else (values #f ans-bads)])))
  (values (and Γ-ok (mk-ok Γ-ok)) ans-bads))

(: Γ+/-AΓ : -M -σ -Γ (-Γ → -AΓ)
   (U (List -WV (Listof -WV) (-Γ → -AΓ))
      (List 'not -WV (Listof -WV) (-Γ → -AΓ))) * → -AΓs)
(define (Γ+/-AΓ M σ Γ mk-ok . filters)
  (define-values (ans-ok ans-bads) (apply Γ+/- M σ Γ mk-ok filters))
  (cond [ans-ok (cond [(set-empty? ans-bads) ans-ok]
                      [else (set-add ans-bads ans-ok)])]
        [else ans-bads]))

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
          (define b-conds (datum->syntax (M-id) (-sexp-and (map mk-cond b-syms doms))))

          (list
           #`[(#,op)
              (match #,(Ws-id)
                [(list #,@b-pats)
                 (cond
                   [#,b-conds
                    (define ans (-b (#,op #,@b-ids)))
                    (values '() (-AΓ (list ans) #,(Γ-id)))]
                   [else ; spurious
                    (printf "Warning: spurious use of unsafe operation ~a~n" '#,op)
                    (values '() ∅)])]
                [_ (values '() (-AΓ -●/Vs #,(Γ-id)))])])]
         
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
         ;; Accumulate clauses for straightforwardly lifted operators
         ;; and names for opaque operators
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
                 [(concrete-impl o)
                  =>
                  (λ ([f : (-M -σ -Γ (Listof -WV) -src-loc → (Values -Δσ -AΓs))])
                    (f M σ Γ Ws l))]
                 [else (values '() (-AΓ -●/Vs Γ))])]
              [else (error 'δ "unhandled: ~a" o)])]))
     ;(printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ : -M -σ -Γ Symbol (Listof -WV) -src-loc → (Values -Δσ -AΓs))
(define (δ M σ Γ o Ws l)
  (gen-δ-body M σ Γ o Ws l))
