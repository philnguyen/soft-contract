#lang typed/racket

(provide δ!)

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
  racket/syntax
  syntax/parse
  racket/contract
  racket/pretty
  racket/list
  racket/function
  racket/contract
  (only-in "../utils/main.rkt" ∋ n-sub mk-cond sexp-and)
  (except-in "../primitives/declarations.rkt" implications base?) "../primitives/utils.rkt")
 )

;; Different kinds of primitives:
;; - Primitives whose domains and ranges are base values (e.g. ariths) : systematically lifted
;; - Other primitives:
;;   * Return `●` by default. Depend on wrapped contract for more precision.
;;   * Do more precise things if defined specially in `concrete` table.
(: concrete-impl : Symbol →
                   (Option (-⟪ℋ⟫ -ℓ -M -σ -Γ (Listof -W¹) → (℘ (Listof -V)))))
;; Table for (semi-)concrete implementations
(define (concrete-impl s)
  (define (error-arity [o : Symbol] [expect : Integer] [given : Integer])
    (error 'δ "Invalid arity uncaught for `~a`: expect ~a, given ~a" o expect given))
  
  (with-args s (⟪ℋ⟫ ℓ M σ Γ Ws)
    [any/c  {set (list -tt)}]
    [none/c {set (list -ff)}]
    [and/c
     (match Ws
       [(list (-W¹ V₁ s₁) (-W¹ V₂ s₂))
        (define α₁ (-α->-⟪α⟫ (or (keep-if-const s₁) (-α.and/c-l ℓ ⟪ℋ⟫))))
        (define α₂ (-α->-⟪α⟫ (or (keep-if-const s₂) (-α.and/c-r ℓ ⟪ℋ⟫))))
        (σ⊕*! σ [α₁ ↦ V₁] [α₂ ↦ V₂])
        (define ℓ₁ (+ℓ/ctc ℓ 0))
        (define ℓ₂ (+ℓ/ctc ℓ 1))
        {set (list (-And/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))}]
       [Ws (error-arity 'and/c 2 (length Ws))])]
    [or/c
     (match Ws
       [(list (-W¹ V₁ s₁) (-W¹ V₂ s₂))
        (define α₁ (-α->-⟪α⟫ (or (keep-if-const s₁) (-α.or/c-l ℓ ⟪ℋ⟫))))
        (define α₂ (-α->-⟪α⟫ (or (keep-if-const s₂) (-α.or/c-r ℓ ⟪ℋ⟫))))
        (σ⊕*! σ [α₁ ↦ V₁] [α₂ ↦ V₂])
        (define ℓ₁ (+ℓ/ctc ℓ 0))
        (define ℓ₂ (+ℓ/ctc ℓ 1))
        {set (list (-Or/C (and (C-flat? V₁) (C-flat? V₂)) (cons α₁ ℓ₁) (cons α₂ ℓ₂)))}]
       [Ws (error-arity 'or/c 2 (length Ws))])]
    [not/c
     (match Ws
       [(list (-W¹ V s))
        (define α (-α->-⟪α⟫ (or (keep-if-const s) (-α.not/c ℓ ⟪ℋ⟫))))
        (σ⊕! σ α V)
        (define ℓ* (+ℓ/ctc ℓ 0))
        {set (list (-Not/C (cons α ℓ*)))}]
       [Ws (error-arity 'not/c 1 (length Ws))])]

    [vector
     (define αs
       (for/list : (Listof -⟪α⟫) ([(W i) (in-indexed Ws)])
         (-α->-⟪α⟫ (-α.idx ℓ ⟪ℋ⟫ (assert i exact-nonnegative-integer?)))))
     (for ([α : -⟪α⟫ αs] [W Ws])
       (σ⊕! σ α (-W¹-V W)))
     {set (list (-Vector αs))}]
    [vector?
     (match Ws
       [(list W)
        (case (MΓ⊢oW M σ Γ 'vector? W)
          [(✓) {set -True/Vs}]
          [(✗) {set -False/Vs}]
          [(?) {set -Bool/Vs}])]
       [_ {set -Bool/Vs}])]
    [vector-length
     (match Ws
       [(list (-W¹ (-Vector αs) _))
        {set (list (-b (length αs)))}]
       [(list (-W¹ (-Vector^ _ n) _))
        {set (list n)}]
       [_ {set -Nat/Vs}])]
    [vectorof
     (match Ws
       [(list (-W¹ V s))
        (define α (-α->-⟪α⟫ (or (keep-if-const s) (-α.vectorof ℓ ⟪ℋ⟫))))
        (σ⊕! σ α V)
        (define ℓ* (+ℓ/ctc ℓ 0))
        {set (list (-Vectorof (cons α ℓ*)))}]
       [Ws (error-arity 'vectorof 1 (length Ws))])]
    [vector/c
     (define-values (αs ℓs)
       (for/lists ([αs : (Listof -⟪α⟫)] [ℓs : (Listof -ℓ)])
                  ([(W i) (in-indexed Ws)] #|TR hack|# #:when (exact-nonnegative-integer? i))
         (match-define (-W¹ _ s) W)
         (values (-α->-⟪α⟫ (or (keep-if-const s)
                               (-α.vector/c ℓ ⟪ℋ⟫ (assert i exact-nonnegative-integer?))))
                 (+ℓ/ctc ℓ i))))
     (for ([α : -⟪α⟫ αs] [W Ws])
       (match-define (-W¹ V _) W)
       (σ⊕! σ α V))
     {set (list (-Vector/C (map (inst cons -⟪α⟫ -ℓ) αs ℓs)))}]
    
    [values {set (map -W¹-V Ws)}]
    
    [void {set -Void/Vs}]
    [arity-includes?
     (match-define (list (-W¹ V_f _) (-W¹ V_n _)) Ws)
     (cond
       [(V-arity V_f) =>
        (λ ([a : Arity])
          (match V_n
            [(-b (? simple-arity? n))
             (define ans (if (arity-includes? a n) -tt -ff))
             {set (list ans)}]
            [else {set -Bool/Vs}]))]
       [else {set -Bool/Vs}])]
    [procedure-arity
     (match-define (list (-W¹ V _)) Ws)
     (cond
       [(V-arity V) => (λ ([a : Arity]) {set (list (-b a))})]
       [else {set -●/Vs}])]

    [equal?
     (case (apply MΓ⊢oW M σ Γ 'equal? Ws)
       [(✓) {set -True/Vs}]
       [(✗) {set -False/Vs}]
       [(?) {set -Bool/Vs}])]
    [eq? ((assert (concrete-impl 'equal?)) ⟪ℋ⟫ ℓ M σ Γ Ws)]
    [= ((assert (concrete-impl 'equal?)) ⟪ℋ⟫ ℓ M σ Γ Ws)]
    
    [procedure?
     (case (apply MΓ⊢oW M σ Γ 'procedure? Ws)
       [(✓) {set -True/Vs}]
       [(✗) {set -False/Vs}]
       [(?) {set -Bool/Vs}])]
    [make-sequence
     {set (list -car -cdr (-● ∅) -cons? -ff -ff)}]

    [make-vector
     {set (list (-● {set 'vector? (-not/c 'immutable?)}))}
     #;(match Ws
       [(list (-W¹ n _) (-W¹ V _))
        (define ⟪α⟫ (-α->-⟪α⟫ (-α.vct ℓ ⟪ℋ⟫)))
        (σ⊕! σ ⟪α⟫ V) ; initilizing, not mutating
        (printf "make-vector initialized with ~a~n" (show-V V))
        {set (list (-Vector^ ⟪α⟫ n))}]
       [_
        (printf "make-vector: skipped~n")
        ∅])]

    [member
     (match Ws
       [(list (-W¹ Vₓ _) (-W¹ Vₗ _))
        (match Vₗ
          [(-Cons _ _)
           (cond
             [(definitely-not-member? σ Vₓ Vₗ)
              {set (list -ff)}]
             [else
              (define ℒ (-ℒ ∅ ℓ))
              (define αₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
              (define αₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
              (define Vₜ (-Cons αₕ αₜ))
              (for ([Vₕ (extract-list-content σ Vₗ)])
                (σ⊕! σ αₕ Vₕ))
              (σ⊕*! σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
              (cond [(definitely-member? σ Vₓ Vₗ) {set (list Vₜ)}]
                    [else                         {set (list Vₜ) (list -ff)}])])]
          [(-b '()) {set (list -ff)}]
          [_ {set (list (-● {set 'list? -cons?}))
                  (list -ff)}])]
       [_ ∅])]
    [memq ((assert (concrete-impl 'member)) ⟪ℋ⟫ ℓ M σ Γ Ws)]
    [memv ((assert (concrete-impl 'member)) ⟪ℋ⟫ ℓ M σ Γ Ws)]

    [append
     (match Ws
       [(list (-W¹ V₁ _) (-W¹ V₂ _))
        (define Vₐ
          (match* (V₁ V₂)
            [((-b null) V₂) V₂]
            [((-Cons αₕ αₜ) V₂)
             (define ℒ (-ℒ ∅ ℓ))
             (define αₕ* (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
             (define αₜ* (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
             (for ([Vₕ (σ@ σ αₕ)])
               (σ⊕! σ αₕ* Vₕ))
             (define Vₜs (set-add (σ@ σ αₜ) V₂))
             (for ([Vₜ* Vₜs])
               (σ⊕! σ αₜ* Vₜ*))
             (-Cons αₕ* αₜ*)]
            [(_ _) (-● {set 'list?})]))
        {set (list Vₐ)}]
       [_ ∅])]

    [getenv
     {set (list (-● {set 'string?}))
          (list -ff)}]

    [reverse
     (match Ws
       [(list (-W¹ Vₗ _))
        (match Vₗ
          [(-b (list)) {set (list -null)}]
          [(-Cons _ _)
           (define ℒ (-ℒ ∅ ℓ))
           (define αₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
           (define αₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
           (define Vₜ (-Cons αₕ αₜ))
           (for ([Vₕ (extract-list-content σ Vₗ)]) (σ⊕! σ αₕ Vₕ))
           (σ⊕*! σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
           {set (list Vₜ)}]
          [(-● ps)
           (cond [(∋ ps -cons?) {set (list (-● {set -cons?}))}]
                 [else          {set (list (-● {set 'list?}))}])]
          [_ {set (list (-● {set 'list?}))}])]
       [_ ∅])]

    [string->list
     (match Ws
       [(list (-W¹ Vₛ _))
        (match Vₛ
          [(-b "") {set (list -null)}]
          [_
           (define ℒ (-ℒ ∅ ℓ))
           (define αₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
           (define αₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
           (define Vₜ (-Cons αₕ αₜ))
           (σ⊕*! σ [αₕ ↦ (-● {set 'char?})]
                   [αₜ ↦ Vₜ]
                   [αₜ ↦ -null])
           (match Vₛ
             [(-b (? string? s)) #:when (> (string-length s) 0)
              {set (list Vₜ)}]
             [_
              {set (list Vₜ)
                (list -null)}])])]
       [_ ∅])]
    
    [list->string
     (match Ws
       [(list (-W¹ Vₗ _))
        {set (list (-● {set 'string?}))}]
       [_ ∅])]

    [list-tail
     (match Ws
       [(list (-W¹ Vₗ _) _)
        (match Vₗ
          [(? -St? Vₗ)
           (define Vₕs (extract-list-content σ Vₗ))
           (define ℒ (-ℒ ∅ ℓ))
           (define αₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
           (define αₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
           (define Vₜ (-Cons αₕ αₜ))
           (for ([Vₕ Vₕs]) (σ⊕! σ αₕ Vₕ))
           (σ⊕*! σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
           {set (list Vₜ)
                (list -null)}]
          [(-b (list))
           {set (list -null)}]
          [_
           {set (list (-● (set 'list?)))}])]
       [_ ∅])]

    [string-append
     {set (list (-● {set 'string?}))}]

    [current-input-port  {set (list (-● {set 'input-port?}))}]
    [current-output-port {set (list (-● {set 'output-port?}))}]
    [current-error-port  {set (list (-● {set 'output-port?}))}]
    [string (set (list (-● {set 'string?})))]
    [read-char {set (list (-● {set 'char?}))}]
    [peek-char {set (list (-● {set 'char?}))}]
    ))

(define-syntax (with-args stx)
  (syntax-parse stx
    [(_ s:id (⟪ℋ⟫:id ℓ:id M:id σ:id Γ:id Ws:id) [t:id e ...] ...)
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
          (λ ([⟪ℋ⟫ : -⟪ℋ⟫] [ℓ : -ℓ] [M : -M] [σ : -σ] [Γ : -Γ] [Ws  : (Listof -W¹)]) : (℘ (Listof -V))
            e ...)]
         ...
         [else #f])]))

;; Language definition for `δ` begins here
(begin-for-syntax
  (define/contract ⟪ℋ⟫-id  (parameter/c identifier?) (make-parameter #f))
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
              (case (apply MΓ⊢oW #,(M-id) #,(σ-id) #,(Γ-id) '#,op #,(Ws-id))
                [(✓) {set -True/Vs}]
                [(✗) {set -False/Vs}]
                [else {set -Bool/Vs}])])]
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

          (define/contract (rng->stx rng)
            (base? . -> . syntax?)
            (match rng
              ['positive? #'{set (->/c 0)}]
              ['negative? #'{set (-</c 0)}]
              [(? symbol? r) #`{set (quote #,r)}]
              [(list 'not/c (? symbol? rng*))
               #`{set (-not/c '#,rng*)}]
              [(list 'and/c rng* ...)
               (define rs (map rng->stx rng*))
               #`{∪ #,@rs}]))
          
          (define refinement-clauses
            (for/list ([ref refinements])
              (match-define `(,dom-chks ... . -> . ,rng-chk) ref)
              (define arg-checks
                (for/list ([dom-chk dom-chks] [W-id W-ids] [e-id e-ids])
                  (match dom-chk
                    [(? symbol? dom/c)
                     #`(eq? '✓ (first-R (p∋Vs #,(σ-id) '#,dom/c (-W¹-V #,W-id))
                                        (Γ⊢e #,(Γ-id) (-?@ '#,dom/c #,e-id))))]
                    [(list 'not/c (? symbol? dom/c*))
                     #`(eq? '✗ (first-R (p∋Vs #,(σ-id) '#,dom/c* (-W¹-V #,W-id))
                                        (Γ⊢e #,(Γ-id) (-?@ '#,dom/c* #,e-id))))])))
              (define precond ; make it a little prettier
                (match arg-checks
                  [(list e) e]
                  [_ #`(and #,@arg-checks)]))
              (define rng/c (rng->stx rng-chk))
              #`(when #,precond
                  (set! Vₐ (V+ #,(σ-id) Vₐ #,rng/c)))))

          ;; Eager refinement is necessary for performance.
          ;; Otherwise even things like (fact _) returns `integer?` rather than `number?`
          ;; need induction from outside
          (define r (rng->stx rng))
          (define maybe-refine
            (cond
              [(null? refinement-clauses)
               #`[_ {set (list (-● #,r))}]]
              [else
               #`[(list #,@W-pats)
                  (define Vₐ : -V (-● #,r))
                  #,@refinement-clauses
                  {set (list Vₐ)}]]))

          (define case-lift
            #`(cond
                [#,b-conds
                 {set (list (-b (#,op #,@b-ids)))}]
                [else ; spurious
                 (printf "Internal: Incorrect use of `~a` flows to `δ`~n" '#,op)
                 ∅]))

          (list
           #`[(#,op)
              (match #,(Ws-id)
                ; straightforward lifting for concrete operands
                [(list #,@b-pats/abs) #,case-lift]
                ;[_ (values ⊥σ (list (-● (set '#,rng))))]
                #,maybe-refine 
                )])]
         
         ; Just return operator name for complicated cases
         [else
          ;(printf "generate-general-clauses: ~a~n" dec)
          (list op)])]

      [dec
       ;(printf "δ: ignore ~a~n" dec)
       '()])))

;; Generate body of `δ`
(define-syntax (gen-δ-body stx)
  (syntax-parse stx
    [(_ ⟪ℋ⟫:id ℓ:id M:id σ:id Γ:id o:id Ws:id)
     (define-values (clauses names)
       (parameterize ([⟪ℋ⟫-id #'⟪ℋ⟫]
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
                (λ ([f : (-⟪ℋ⟫ -ℓ -M -σ -Γ (Listof -W¹) → (℘ (Listof -V)))])
                  (f ⟪ℋ⟫ ℓ M σ Γ Ws))]
               [else
                (case o
                  #,@clauses
                  [else {set -●/Vs}])])
             (error 'δ "unhandled: ~a" o)))
     ;(printf "Generated:~n~a~n" (pretty (syntax->datum body-stx)))
     body-stx]))

(: δ! : -⟪ℋ⟫ -ℓ -M -σ -Γ Symbol (Listof -W¹) → (℘ (Listof -V)))
;; Return possible answers for primitives
(define (δ! ⟪ℋ⟫ ℓ M σ Γ o Ws)
  (with-debugging/off ((ans) (gen-δ-body ⟪ℋ⟫ ℓ M σ Γ o Ws))
    (case o
      [(eq?) ;(reverse memq)
       (when #t #;(equal? ans (set (-● {set 'exact-integer?})))
         (printf "δ: ~a~n" o)
         (define-set αs : -α)
         (for ([W Ws])
           (αs-union! (V->αs (-W¹-V W)))
           (printf " - ~a~n" (show-W¹ W)))
         (printf "ans:~n")
         (for ([a ans])
           (printf " -")
           (for ([V a])
             (αs-union! (V->αs V))
             (printf " ~a" (show-V V)))
           (printf "~n"))
         (printf "store:~n")
         (for ([r (show-σ (span-σ (-σ-m σ) αs))])
           (printf " - ~a~n" r))
         (printf "~n"))])))

(: definitely-member? : -σ -V -St → Boolean)
(define (definitely-member? σ V Vₗ)
  (let loop ([Vₗ : -V Vₗ] [seen : (℘ -V) ∅])
    (cond
      [(∋ seen Vₗ) #f]
      [else
       (match Vₗ
         [(-Cons αₕ αₜ)
          (or (for/and : Boolean ([Vₕ (σ@ σ αₕ)]) (definitely-equal? σ V Vₕ))
              (for/and : Boolean ([Vₜ (σ@ σ αₜ)]) (loop Vₜ (set-add seen Vₗ))))]
         [_ #f])])))

(: definitely-not-member? : -σ -V -St → Boolean)
(define (definitely-not-member? σ V Vₗ)
  (let loop ([Vₗ : -V Vₗ] [seen : (℘ -V) ∅])
    (cond
      [(∋ seen Vₗ) #t]
      [else
       (match Vₗ
         [(-Cons αₕ αₜ)
          (and (for/and : Boolean ([Vₕ (σ@ σ αₕ)]) (definitely-not-equal? σ V Vₕ))
               (for/and : Boolean ([Vₜ (σ@ σ αₜ)]) (loop Vₜ (set-add seen Vₗ))))]
         [(-b (list)) #t]
         [_ #f])])))


(: definitely-equal? : -σ -V -V → Boolean)
(define (definitely-equal? σ V₁ V₂)
  (let loop ([V₁ : -V V₁] [V₂ : -V V₂] [seen : (℘ (Pairof -V -V)) ∅])
    (cond
      [(∋ seen (cons V₁ V₂)) #t]
      [else
       (match* (V₁ V₂)
         [((-b b₁) (-b b₂)) (equal? b₁ b₂)]
         [((-St 𝒾 αs₁) (-St 𝒾 αs₂))
          (for/and : Boolean ([α₁ : -⟪α⟫ αs₁] [α₂ : -⟪α⟫ αs₂])
            (define Vs₁ (σ@ σ α₁))
            (define Vs₂ (σ@ σ α₂))
            (for/and : Boolean ([V₁* Vs₁]) ; can't use for*/and :(
              (for/and : Boolean ([V₂* Vs₂])
                (loop V₁* V₂* (set-add seen (cons V₁ V₂))))))]
         [(_ _) #f])])))

(: definitely-not-equal? : -σ -V -V → Boolean)
(define (definitely-not-equal? σ V₁ V₂)
  (let loop ([V₁ : -V V₁] [V₂ : -V V₂] [seen : (℘ (Pairof -V -V)) ∅])
    (cond
      [(∋ seen (cons V₁ V₂)) #t]
      [else
       (match* (V₁ V₂)
         [((-b b₁) (-b b₂)) (not (equal? b₁ b₂))]
         [((-St 𝒾₁ αs₁) (-St 𝒾₂ αs₂))
          (or (not (equal? 𝒾₁ 𝒾₂))
              (for/or : Boolean ([α₁ : -⟪α⟫ αs₁] [α₂ : -⟪α⟫ αs₂])
                (define Vs₁ (σ@ σ α₁))
                (define Vs₂ (σ@ σ α₂))
                (for/and : Boolean ([V₁ Vs₁])
                  (for/and : Boolean ([V₂ Vs₂])
                    (loop V₁ V₂ (set-add seen (cons V₁ V₂)))))))]
         [(_ _) #f])])))

(module+ test
  (require typed/rackunit)
  
  (: check-δ/b : Symbol (Listof Base) Base → Any)
  ;; Test δ's concrete fragment
  (define (check-δ/b o bs bₐ)
    (define Ws (for/list : (Listof -W¹) ([b bs]) (-W¹ (-b b) (-b b))))
    (define Vs (δ! ⟪ℋ⟫∅ +ℓ₀ (⊥M) (⊥σ) ⊤Γ o Ws))
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
