#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "utils.rkt" "ast.rkt" "runtime.rkt" "provability.rkt"
 (for-syntax racket/base racket/match racket/syntax syntax/parse racket/contract
             racket/pretty racket/list racket/function racket/contract
             "untyped-macros.rkt" "utils.rkt" "prims.rkt")
 )
(provide δ Γ+/- -list•)

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Struct primitives (e.g. constructors, predicates, accessors, mutators): systematically generated
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.

(: concrete : Symbol → (Option (-M -σ -Γ (Listof -WV) -src-loc → (Values -σ -AΓs))))
;; Concrete table for unsafe operations
(define (concrete s)
  (define-syntax-rule (with-args (M σ Γ Ws loc) [t e ...] ...)
    (case s
      [(t)
       (λ ([M : -M] [σ : -σ] [Γ : -Γ] [Ws  : (Listof -WV)] [loc : -src-loc])
         e ...)]
      ...
      [else #f]))
  
  (with-args (M σ Γ Ws loc)
    ))

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

(define -list• : (List -V) (list '•))

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

  (define/contract (mk-quote id)
    (identifier? . -> . syntax?)
    #`(quote #,(syntax->datum id)))

  (define/contract (generate-general-clauses dec)
    (dec? . -> . (listof syntax?))

    ;(printf "Generating for ~a~n" (syntax->datum row))

    (define/contract ctx syntax? (M-id))

    (define/contract (mk-struct-info t mut?s)
      (symbol? (listof boolean?) . -> . syntax?)
      (define muts (for/list ([(mut? i) (in-indexed mut?s)] #:when mut?) i))
      (define n (length mut?s))
      #`(-struct-info #,t #,n (set #,@(muts))))

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
           `(#:struct-mut ,_ ...))
       '()]

      ;; Handle generate case
      [`(,(? symbol? op) ,(? arr? main) ,(? arr? refinements) ... #:other-errors (,guards ...) ...)

       (define/contract mk-pat (any/c . -> . syntax?)
         (match-lambda
           [(? symbol? p) #`(? #,p)]
           [`(not/c ,(? symbol? p)) #`(not (? #,p))]
           [`(and/c ,ps ...) #`(and #,@(map mk-pat ps))]))

       (define-values (doms rng)
         (match-let ([`(,x ... . -> . ,y) main])
           (values x y)))
            
       (define/contract rhs syntax?
         (cond
           ; Operations on base values are straightforward to lift
           [(and (andmap base? doms) (base? rng))

            (define/contract b-ids (listof identifier?)
              (build-list (length doms) (curry mk-sym 'b)))

            (define pat-bs
              (for/list ([b-id b-ids] [p doms])
                (define stx-b
                  (match p
                    [(? symbol? p) #`(-b (? #,p #,b-id))]
                    [`(not/c ,(? symbol? p)) #`(-b (not (? #,p #,b-id)))]
                    [`(and/c ,ps ...)
                     #`(-b (and #,@(map mk-pat ps) #,b-id))]
                    [`(or/c ,ps ...)
                     #`(-b (and (or #,@(map mk-pat ps)) #,b-id))]))
                #`(-W _ #,stx-b)))

            (define/contract e-ids (listof identifier?)
              (build-list (length doms) (curry mk-sym 'e)))

            #`(match #,(Ws-id)
                [(list #,@pat-bs)
                 (define ans (-b (#,op #,@b-ids)))
                 (values #,(σ-id) (-AΓ (list ans) #,(Γ-id)))]
                [_ (values #,(σ-id) (-AΓ -list• #,(Γ-id)))])]
           ; Other operations return `●` by default
           [else
            #`(cond
                [(concrete '#,op)
                 =>
                 (λ ([f : (-M -σ -Γ (Listof -WV) -src-loc → (Values -σ -AΓs))])
                   (f #,(M-id) #,(σ-id) #,(Γ-id) #,(Ws-id) #,(l-id)))]
                [else (values #,(σ-id) (-AΓ -list• #,(Γ-id)))])]))
       
       ;; generate lhs-rhs for specific `op`
       (list #`[(#,op) #,rhs])]

      [dec
       (printf "δ: ignore ~a~n" dec)
       '()])))

;; Generate body of `δ`
(define-syntax (gen-δ-body stx)
  (syntax-parse stx
    [(_ M:id σ:id Γ:id o:id Ws:id l:id)
     (define clauses
       (parameterize ([M-id #'M]
                      [σ-id #'σ]
                      [Γ-id #'Γ]
                      [o-id #'o]
                      [Ws-id #'Ws]
                      [l-id #'l])
         (append-map generate-general-clauses prims)))
     (define body-stx
       #`(case o
           #,@clauses
           [else (error 'δ "unhandled: ~a" o)]))
     (printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ : -M -σ -Γ Symbol (Listof -WV) -src-loc → (Values -σ -AΓs))
(define (δ M σ Γ o Ws l)
  (gen-δ-body M σ Γ o Ws l))
