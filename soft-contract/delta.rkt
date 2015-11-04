#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "utils.rkt" "ast.rkt" "runtime.rkt" "provability.rkt"
 (for-syntax racket/base racket/syntax syntax/parse racket/contract
             racket/pretty racket/list racket/function racket/contract
             "untyped-macros.rkt" "utils.rkt" "prims.rkt")
 )
(provide δ Γ+/-)

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Struct primitives (e.g. constructors, predicates, accessors, mutators): systematically generated
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.

;; Concrete table for unsafe operations
;(: δ : -M -σ -Γ -o (Listof -WV) Mon-Party → -AΓs)
(: concrete : Symbol → (Option (-M -σ -Γ (Listof -WV) → -AΓs)))
(define (concrete s)
  (case s
    [else #f]))

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

(: apply-st-mk : -struct-info -M -σ -Γ (Listof -WV) Mon-Party → -AΓs)
(define (apply-st-mk si M σ Γ Ws l)
  (error "TODO"))

(: apply-st-p : -struct-info -M -σ -Γ (Listof -WV) Mon-Party → -AΓs)
(define (apply-st-p si M σ Γ Ws l)
  (error "TODO"))

(: apply-st-ac : -struct-info Integer -M -σ -Γ (Listof -WV) Mon-Party → -AΓs)
(define (apply-st-ac si Integer M σ Γ Ws l)
  (error "TODO"))

(: apply-st-mut : -struct-info Integer -M -σ -Γ (Listof -WV) Mon-Party → -AΓs)
(define (apply-st-mut si Integer M σ Γ Ws l)
  (error "TODO"))

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

  (define/hack (convert-syntax stx)
    (datum->syntax #'here stx))

  (define-syntax-class rng
    #:description "limited contract range"
    (pattern (~or c:ctc ((~literal values) d:ctc ...))))

  (define-syntax-class arr
    #:description "limited function contract"
    (pattern ((~literal ->) dom:ctc ... rng:ctc #;rng:rng)))

  (define-syntax-class arr*
    #:description "limited vararg contract"
    (pattern ((~literal ->*) (dom:ctc ...) #:rest rest:ctc rng:rng)))

  (define-syntax-class ctc
    #:description "limited contract"
    (pattern (~or x:id
                  ((~literal not/c) c:ctc)
                  ((~literal one-of/c) d:ctc ...)
                  ((~literal and/c) d:ctc ...)
                  ((~literal or/c) d:ctc ...)
                  ((~literal listof) c:ctc)
                  ((~literal list/c) d:ctc ...)
                  ((~literal cons/c) l:ctc r:ctc)
                  a:arr
                  a:arr*)))

  (define/contract (generate-general-clauses row)
    (syntax? . -> . (listof syntax?))

    ;(printf "Generating for ~a~n" (syntax->datum row))

    (define/contract (mk-struct-info t mut?s)
      (symbol? (listof boolean?) . -> . syntax?)
      (define muts (for/list ([(mut? i) (in-indexed mut?s)] #:when mut?) i))
      (define n (length mut?s))
      #`(-struct-info #,t #,n (set #,@(muts))))

    (syntax-parse row

      ;; Expand shorthand cases
      [(#:pred p:id)
       (generate-general-clauses #'(p (any/c . -> . boolean?) #:other-errors))]
      [(#:pred p:id (dom:ctc ...))
       (generate-general-clauses #'(p (dom ... . -> . boolean?) #:other-errors))]
      [(#:batch (ops:id ...) main:ctc refinements:ctc ...)
       (append-map
        (λ (op) (generate-general-clauses #`(#,op main refinements ...)))
        (syntax->list #'(ops ...)))]
      [(op:id main:ctc refinements:ctc ...)
       (generate-general-clauses #'(op main refinements ... #:other-errors))]

      ;; Ignore non-symbol cases
      [(~or (#:struct-cons _ ...)
            (#:struct-pred _ ...)
            (#:struct-acc _ ...)
            (#:struct-mut _ ...))
       '()]

      ;; Handle generate case
      [(op:id main:arr refinements:arr ... #:other-errors (guards:ctc ...) ...)

       (define (mk-pat c)
         (syntax-parse c
           [p:id #`(? p)]
           [((~literal not/c) p:id) #`(not (? p))]
           [((~literal and/c) p ...)
            #`(and #,@(map mk-pat (syntax->list #'(p ...))))]))

       (define-values (doms rng)
         (syntax-parse #'main
           [(x:ctc ... . (~literal ->) . y:ctc)
            (values (syntax->list #'(x ...)) #'y)]))

       (define rhs
         (cond
           ; Operations on base values are straightforward to lift
           [(and (andmap (compose base? syntax->datum) doms)
                 (base? (syntax->datum rng)))

            (define/contract b-ids (listof identifier?)
              (build-list (length doms) (λ (i) (datum->syntax #'op (mk-sym 'b i)))))

            (define pat-bs
              (for/list ([b-id b-ids] [p doms])
                (define stx-b
                  (syntax-parse p
                    [p:id #`(-b (? p #,b-id))]
                    [((~literal not/c) p:id) #`(-b (not (? p #,b-id)))]
                    [((~literal and/c) p ...)
                     #`(-b (and #,@(map mk-pat (syntax->list #'(p ...))) #,b-id))]
                    [((~literal or/c) p ...)
                     #`(-b (or #,@(map mk-pat (syntax->list #'(p ...))) #,b-id))]))
                #`(-W _ #,stx-b)))

            (define/contract e-ids (listof identifier?)
              (build-list (length doms) (λ (i) (datum->syntax #'op (mk-sym 'e i)))))
            
            #`(match #,(Ws-id)
                [(list #,@pat-bs)
                 (define ans (-b (op #,@b-ids)))
                 (-AΓ (list ans) #,(Γ-id))]
                [_
                 (-AΓ -list• #,(Γ-id))])]
           ; Other operations return `●` by default
           [else #`(-AΓ -list• #,(Γ-id))]))
       
       ;; generate lhs-rhs for specific `op`
       (list #`[(op) #,rhs])]
      [stx
       (printf "`generate-general-clauses`: ignore ~a~n" (syntax->datum #'stx))
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
         (append-map generate-general-clauses
                     (syntax->list (convert-syntax prims)))))
     (define body-stx
       #`(match o
           [(? symbol? s)
            (case o
              #,@clauses
              [else (error 'δ "unhandled: ~a" o)])]
           [(-st-mk si) (apply-st-mk si M σ Γ Ws l)]
           [(-st-p si) (apply-st-p si M σ Γ Ws l)]
           [(-st-ac si i) (apply-st-ac si i M σ Γ Ws l)]
           [(-st-mut si i) (apply-st-mut si i M σ Γ Ws l)]
           [x (error 'δ "unhandled: ~a" x)]))
     (printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ : -M -σ -Γ -o (Listof -WV) Mon-Party → -AΓs)
(define (δ M σ Γ o Ws l)
  (gen-δ-body M σ Γ o Ws l))
