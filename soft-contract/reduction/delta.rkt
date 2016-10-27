#lang typed/racket
(require
 racket/flonum racket/extflonum math/base
 "../utils/main.rkt"
 "../primitives/utils.rkt"
 "../ast/definition.rkt"
 "../runtime/main.rkt"
 "../proof-relation/main.rkt"
 (for-syntax
  racket/base
  racket/match
  (except-in racket/syntax format-symbol)
  syntax/parse
  racket/contract
  racket/pretty
  (except-in racket/list remove-duplicates)
  racket/function
  racket/contract
  "../utils/main.rkt"
  (except-in "../primitives/declarations.rkt" implications base?) "../primitives/utils.rkt")
 )
(provide δ!)

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Struct primitives (e.g. constructors, predicates, accessors, mutators): systematically generated
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.
;; Result of `δ` needs not be deterministic, because it can return abstract value
;; representing multiple ones, and errors should have been taken care of by
;; contracts. (These are unsafe primitives).
;; `δ` needs not refine path condition
(: concrete-impl : Symbol →
                   (Option (-𝒞 -ℓ -M -σ -Γ (Listof -W¹) → (Option (Listof -V)))))
;; Table for (semi-)concrete implementations
(define (concrete-impl s)
  (define (error-arity [o : Symbol] [expect : Integer] [given : Integer])
    (error 'δ "Invalid arity uncaught for `~a`: expect ~a, given ~a" o expect given))
  
  (with-args s (𝒞 l ℓ M σ Γ Ws)
    [any/c  (list -tt)]
    [none/c (list -ff)]
    [and/c
     (match Ws
       [(list (-W¹ V₁ s₁) (-W¹ V₂ s₂))
        (define α₁ (or (keep-if-const s₁) (-α.and/c-l ℓ 𝒞)))
        (define α₂ (or (keep-if-const s₂) (-α.and/c-r ℓ 𝒞)))
        (σ⊔*! σ [α₁ ↦ V₁ #t] [α₂ ↦ V₂ #t])
        (define ℓ₁ (+ℓ/ctc ℓ 0))
        (define ℓ₂ (+ℓ/ctc ℓ 1))
        (list (-And/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))]
       [Ws (error-arity 'and/c 2 (length Ws))])]
    [or/c
     (match Ws
       [(list (-W¹ V₁ s₁) (-W¹ V₂ s₂))
        (define α₁ (or (keep-if-const s₁) (-α.or/c-l ℓ 𝒞)))
        (define α₂ (or (keep-if-const s₂) (-α.or/c-r ℓ 𝒞)))
        (σ⊔*! σ [α₁ ↦ V₁ #t] [α₂ ↦ V₂ #t])
        (define ℓ₁ (+ℓ/ctc ℓ 0))
        (define ℓ₂ (+ℓ/ctc ℓ 1))
        (list (-Or/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))]
       [Ws (error-arity 'or/c 2 (length Ws))])]
    [not/c
     (match Ws
       [(list (-W¹ V s))
        (define α (or (keep-if-const s) (-α.not/c ℓ 𝒞)))
        (σ⊔! σ α V #t)
        (define ℓ* (+ℓ/ctc ℓ 0))
        (list (-Not/C (cons α ℓ*)))]
       [Ws (error-arity 'not/c 1 (length Ws))])]

    [vector
     (define αs
       (for/list : (Listof -α.idx) ([(W i) (in-indexed Ws)])
         (-α.idx ℓ 𝒞 (assert i exact-nonnegative-integer?))))
     (for ([α αs] [W Ws])
       (σ⊔! σ α (-W¹-V W) #t))
     (list (-Vector αs))]
    [vector?
     (match Ws
       [(list W)
        (case (MΓ⊢oW M Γ 'vector? W)
          [(✓) -True/Vs]
          [(✗) -False/Vs]
          [(?) -Bool/Vs])]
       [_ -Bool/Vs])]
    [vector-length
     (match Ws
       [(list (-W¹ (-Vector αs) _))
        (list (-b (length αs)))]
       [_ -Nat/Vs])]
    [vectorof
     (match Ws
       [(list (-W¹ V s))
        (define α (or (keep-if-const s) (-α.vectorof ℓ 𝒞)))
        (σ⊔! σ α V #t)
        (define ℓ* (+ℓ/ctc ℓ 0))
        (list (-Vectorof (cons α ℓ*)))]
       [Ws (error-arity 'vectorof 1 (length Ws))])]
    [vector/c
     (define-values (αs ℓs)
       (for/lists ([αs : (Listof (U -α.cnst -α.vector/c))] [ℓs : (Listof -ℓ)])
                  ([(W i) (in-indexed Ws)] #|TR hack|# #:when (exact-nonnegative-integer? i))
         (match-define (-W¹ _ s) W)
         (values (or (keep-if-const s) (-α.vector/c ℓ 𝒞 (assert i exact-nonnegative-integer?)))
                 (+ℓ/ctc ℓ i))))
     (for ([α αs] [W Ws])
       (match-define (-W¹ V _) W)
       (σ⊔! σ α V #t))
     (list (-Vector/C (map (inst cons (U -α.cnst -α.vector/c) -ℓ) αs ℓs)))]
    
    [values (map -W¹-V Ws)]
    
    [void -Void/Vs]
    [arity-includes?
     (match-define (list (-W¹ V_f _) (-W¹ V_n _)) Ws)
     (cond
       [(V-arity V_f) =>
        (λ ([a : Arity])
          (match V_n
            [(-b (? simple-arity? n))
             (define ans (if (arity-includes? a n) -tt -ff))
             (list ans)]
            [else -Bool/Vs]))]
       [else -Bool/Vs])]
    [procedure-arity
     (match-define (list (-W¹ V _)) Ws)
     (cond
       [(V-arity V) => (λ ([a : Arity]) (list (-b a)))]
       [else -●/Vs])]

    [equal?
     (case (apply MΓ⊢oW M Γ 'equal? Ws)
       [(✓) (list -tt)]
       [(✗) (list -ff)]
       [(?) -Bool/Vs])]

    [eq? ; duplicate of `equal?`. TODO: why didn't I just `(or equal? eq? =)`??
     (case (apply MΓ⊢oW M Γ 'equal? Ws)
       [(✓) (list -tt)]
       [(✗) (list -ff)]
       [(?) -Bool/Vs])]

    [= ; duplicate of `equal?` (args already guarded by contracts)
     (case (apply MΓ⊢oW M Γ 'equal? Ws)
       [(✓) (list -tt)]
       [(✗) (list -ff)]
       [(?) -Bool/Vs])]
    
    [procedure?
     (case (apply MΓ⊢oW M Γ 'procedure? Ws)
       [(✓) (list -tt)]
       [(✗) (list -ff)]
       [(?) -Bool/Vs])]
    [make-sequence
     (list -car -cdr (-● ∅) -cons? -ff -ff)]
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
          (λ ([𝒞 : -𝒞] [ℓ : -ℓ] [M : -M] [σ : -σ] [Γ : -Γ] [Ws  : (Listof -W¹)]) : (Option (Listof -V))
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

      ;; Handle general case
      [`(,(and (? symbol?) (not (? ignore-for-now?)) op)
          (,doms ... . -> . ,rng) ,(? arr? refinements) ...
         #:other-errors (,guards ...) ...)

       (cond
         ; Return case clause for straightforward lifting of predicates
         [(∋ base-predicates op)
          (list
           #`[(#,op)
              (case (apply MΓ⊢oW #,(M-id) #,(Γ-id) '#,op #,(Ws-id))
                [(✓) (list -tt)]
                [(✗) (list -ff)]
                [else -Bool/Vs])])]
         ; Return case clause for straightforward lifting of other 1st order operators
         [(and (andmap base? doms) (base? rng))
          (define/contract b-syms (listof symbol?)
            (build-list (length doms) (λ (i) (format-symbol "e~a" (n-sub i)))))
          (define/contract b-ids (listof identifier?) (map (curry datum->syntax (M-id)) b-syms))
          (define b-pats/abs  (for/list ([b-id b-ids]) #`(-W¹ _ (-b #,b-id))))
          (define b-pats/conc (for/list ([b-id b-ids]) #`(-W¹ (-b #,b-id) _)))
          (define b-conds (datum->syntax (M-id) (sexp-and (map mk-cond b-syms doms))))

          (define-values (W-pats W-ids e-ids)
            (for/lists (W-pats W-ids e-ids) ([i (length doms)])
              (define W-id (datum->syntax (M-id) (format-symbol "W~a" (n-sub i))))
              (define e-id (datum->syntax (M-id) (format-symbol "e~a" (n-sub i))))
              (values #`(and #,W-id (-W¹ _ #,e-id)) W-id e-id)))
          
          (define refinement-clauses
            (for/list ([ref refinements])
              (match-define `(,dom-chks ... . -> . ,rng-chk) ref)
              (define arg-checks
                (for/list ([dom-chk dom-chks] [W-id W-ids] [e-id e-ids])
                  (match dom-chk
                    [(? symbol? dom/c)
                     #`(eq? '✓ (first-R (p∋Vs '#,dom/c (-W¹-V #,W-id))
                                        (Γ⊢e #,(Γ-id) (-?@ '#,dom/c #,e-id))))]
                    [(list 'not/c (? symbol? dom/c*))
                     #`(eq? '✗ (first-R (p∋Vs '#,dom/c* (-W¹-V #,W-id))
                                        (Γ⊢e #,(Γ-id) (-?@ '#,dom/c* #,e-id))))])))
              (define precond ; make it a little prettier
                (match arg-checks
                  [(list e) e]
                  [_ #`(and #,@arg-checks)]))
              (define rng/c
                (match rng-chk
                  ['positive? #'(-λ '(𝒙) (-@ '< (list (-b 0) (-x '𝒙)) +ℓ₀))]
                  ['negative? #'(-λ '(𝒙) (-@ '< (list (-x '𝒙) (-b 0)) +ℓ₀))]
                  [(? symbol? rng/c) #`(quote #,rng/c)]
                  [(list 'not/c (? symbol? rng/c*))
                   #`(-@ 'not/c (list '#,rng/c*) +ℓ₀)]))
              #`(when #,precond
                  (set! Vₐ (V+ #,(σ-id) Vₐ #,rng/c)))))

          ;; Eager refinement is necessary for performance.
          ;; Otherwise even things like (fact _) returns `integer?` rather than `number?`
          ;; need induction from outside
          (define maybe-refine
            (cond
              [(null? refinement-clauses)
               #`[_ (list (-● {set '#,rng}))]]
              [else
               #`[(list #,@W-pats)
                  (define Vₐ : -V (-● {set '#,rng}))
                  #,@refinement-clauses
                  (list Vₐ)]]))

          (define case-lift
            #`(cond
                [#,b-conds
                 (list (-b (#,op #,@b-ids)))]
                [else ; spurious
                 (printf "Internal: Incorrect use of `~a` flows to `δ`~n" '#,op)
                 #f]))

          (list
           #`[(#,op)
              (match #,(Ws-id)
                ; straightforward lifting for concrete operands
                [(list #,@b-pats/abs) #,case-lift]
                ;[_ (values ⊥σ (list (-● (set '#,rng))))]
                #,maybe-refine 
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
                (λ ([f : (-𝒞 -ℓ -M -σ -Γ (Listof -W¹) → (Option (Listof -V)))])
                  (f 𝒞 ℓ M σ Γ Ws))]
               [else
                (case o
                  #,@clauses
                  [else -●/Vs])])
             (error 'δ "unhandled: ~a" o)))
     ;(printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ! : -𝒞 -ℓ -M -σ -Γ Symbol (Listof -W¹) → (Option (Listof -V)))
(define (δ! 𝒞 ℓ M σ Γ o Ws)
  (with-debugging/off ((ans) (gen-δ-body 𝒞 ℓ M σ Γ o Ws))
    (when (equal? o '>=)
      (printf "δ ~a ~a -> ~a~n" (show-o o) (map show-W¹ Ws) (and ans (map show-V ans))))))


(module+ test
  (require typed/rackunit)
  
  (: check-δ/b : Symbol (Listof Base) Base → Any)
  ;; Test δ's concrete fragment
  (define (check-δ/b o bs bₐ)
    (define Ws (for/list : (Listof -W¹) ([b bs]) (-W¹ (-b b) (-b b))))
    (define Vs (δ! 𝒞∅ +ℓ₀ (⊥M) (⊥σ) ⊤Γ o Ws))
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
