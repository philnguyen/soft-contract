#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "ast.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Path invariant represented by expressions known to evaluate to truth
;; independent of mutable states
;; The bindings `(x ≡ e)` are just a way of storing `(equal? x e)`
;; for faster queries
(struct -Γ ([bindings : (Map Symbol -e)] [facts : -es]) #:transparent)
(define -Γ⊤ (-Γ (hash) ∅))
(define-type/pred -?e (Option -e))

(: canonicalize : (U -Γ (Map Symbol -e)) (U Symbol -e) → -e)
;; Rewrite invariant in terms of lexically farthest variables possible
(define (canonicalize Γ+bnds e)
  (define bnds (if (-Γ? Γ+bnds) (-Γ-bindings Γ+bnds) Γ+bnds))
  (match e ; avoid creating new objects in special cases
    [(or (? symbol? x) (-x x))
     (assert x) ; hack for TR
     (hash-ref bnds x (λ () (-x x)))]
    [(? -e?)
     (for/fold ([e* : -e e]) ([(x ex) bnds])
       (e/ e* x ex))]))

(: Γ↓ : -Γ (Setof Symbol) → -Γ)
;; Restrict path invariant to given variables
(define (Γ↓ Γ xs)
  (match-define (-Γ bnds facts) Γ)
  (cond ; avoid creating new identical object
    [(equal? xs (dom bnds)) Γ]
    [else
     (define bnds*
       ; should be the case: x ∈ xs ⇒ FV⟦bnds(e)⟧ ⊆ xs
       (for/hash : (Map Symbol -e) ([(x e) bnds] #:when (∋ xs x))
         (values x e)))
     (define facts*
       (for/set: : -es ([e facts] #:when (⊆ (FV e) xs)) e))
     (-Γ bnds* facts*)]))

(: Γ+ : -Γ -?e * → -Γ)
;; Extend path invariant
(define (Γ+ Γ . es)
  (match-define (-Γ bnds facts) Γ)
  (define facts*
    (for/fold ([facts* : -es facts]) ([e es] #:when e)
      (set-add facts* (canonicalize bnds e))))
  (-Γ bnds facts*))

(: Γ-bind : -Γ Symbol -?e → -Γ)
;; Extend path invariant with given binding
(define (Γ-bind Γ x e)
  (cond
    [e
     (match-define (-Γ bnds facts) Γ)
     (-Γ (hash-set bnds x (canonicalize bnds e)) facts)]
    [else Γ]))

(: Γ-invalidate : -Γ Symbol → -Γ)
;; Discard all propositions in `Γ` involving `x`
(define (Γ-invalidate Γ x)
  (match-define (-Γ bnds facts) Γ)
  (define bnds*
    (for/hash : (Map Symbol -e)
              ([(z ez) bnds] #:unless (or (equal? z x) (∋ (FV ez) x)))
      (values z ez)))
  (define facts* (for/set: : -es ([e facts] #:unless (∋ (FV e) x)) e))
  (-Γ bnds* facts*))

(: Γ-reset : -Γ Symbol -?e → -Γ)
;; Reset binding for variable `x`
(define (Γ-reset Γ x e)
  (Γ-bind (Γ-invalidate Γ x) x e))

(: FV-Γ : -Γ → (Setof Symbol))
(define (FV-Γ Γ) (dom (-Γ-bindings Γ)))

(: Γ/ : -Γ Symbol -e → -Γ)
(define (Γ/ Γ x e)
  (match-define (-Γ bnds facts) Γ)
  ; if variable is an alias for another expression `eₓ`,
  ; perform substitution in terms of that expression `eₓ`
  (define pt : (U Symbol -e) (hash-ref bnds x (λ () x)))
  (define bnds*
    (for/hash : (Map Symbol -e) ([(x e₀) bnds]) (values x (e/ e₀ pt e))))
  (define facts*
    (for/set: : -es ([e₀ facts]) (e/ e₀ pt e)))
  (-Γ bnds* facts*))

(: Γ-binds? : -Γ Symbol → Boolean)
;; Check if variable is bound in path invariant
(define (Γ-binds? Γ x)
  (hash-has-key? (-Γ-bindings Γ) x))

(: Γ-has? : -Γ -?e → Boolean)
;; Check if `Γ` readily remembers `e`
(define (Γ-has? Γ e) (∋ (-Γ-facts Γ) e))

(define (show-?e [e : -?e]) : Sexp
  (cond [e (show-e e)]
        [else '⊘]))

(: show-Γ : -Γ → (Listof Sexp))
(define (show-Γ Γ)
  (match-define (-Γ bnds facts) Γ)
  `(,@(for/list : (Listof Sexp) ([(x e) bnds])
        `(≡ ,x ,(show-e e)))
    ,@(for/list : (Listof Sexp) ([e facts])
        (show-e e))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Evaluated value
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; blessed arrow, struct, and closed lambda, etc.
(define-data -V
  'undefined
  -prim
  '•
  (struct -Ar
    [xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)]
    [rng : -e] [env : -ρ] [Γ : -Γ]
    [v : -α] [l³ : Mon-Info])
  (struct -St [info : -struct-info] [fields : (Listof -α)])
  (struct -Vector [fields : (Listof -α)])
  (struct -Clo* [xs : -formals] [e : -e] [ρ : -ρ]) ; unescaped closure
  (struct -Clo [xs : -formals] [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -=>i
    [xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)]
    [rng : -e] [env : -ρ] [Γ : -Γ])
  (struct -St/C [info : -struct-info] [fields : (Listof -α)])
  (struct -μ/C [x : Symbol] [c : -α])
  (struct -X/C [ref : -α]))
(define-type -Vs (Listof -V))

(define-data -A
  -Vs
  (struct -blm [violator : Mon-Party] [origin : Mon-Party] [v : -V] [c : -Vs]))

;; `X` paired with expression
(struct (X) -W ([x : X] [e : -?e]) #:transparent)

(define-type/pred -WV (-W -V))
(define-type -WVs (-W (Listof -V)))

(define (WVs->Vs [WVs : (Listof -WV)]) : -Vs
  ((inst map -V -WV) -W-x WVs))

(: close : -v -ρ → -V)
;; Create closure from value syntax and environment
(define (close v ρ)
  (match v
    [(-λ xs e) (-Clo* xs e (ρ↓ ρ (FV v)))]
    [(? -prim? v) v]
    [(? -•ₗ? v) '•]
    [_ (error 'close "Not yet supported: ~a" v)]))

(: close-Γ (case-> [-Γ -V → -V]
                   [-Γ (Listof -V) → (Listof -V)]))
(define (close-Γ Γ V)
  (match V
    [(-Clo* xs e ρ)
     (-Clo xs e ρ (Γ↓ Γ (dom ρ)))]
    [(list Vs ...) (map (curry close-Γ Γ) Vs)]
    [(? -V?) V]))

(: C-flat? : -σ -V → Boolean)
;; Check whether value is a flat contract
(define (C-flat? σ V)
  (define (C-flat/list? [αs : (Listof -α)]) : Boolean
    ;; TODO: can't do for*/and in TR
    (for/and ([α αs])
      (for/and : Boolean ([V (σ@ σ α)])
        (C-flat? σ V))))
  (match V
    [(-St (or 'and/c 'or/c 'not/c) αs) (C-flat/list? αs)]
    [(-St/C _ αs) (C-flat/list? αs)]
    [(? -=>i?) #f]
    [(-μ/C _ α) (for/and : Boolean ([V (σ@ σ α)]) (C-flat? σ V))]
    [_ #t]))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    ['• '●]
    [(? -o? o) (show-o o)]
    [(-Clo* xs e _) (show-e (-λ xs e))]
    [(-Clo xs e _ _) (show-e (-λ xs e))]
    [(-Ar xs cs γs rng env Γ α l³)
     `((,@(for/list : (Listof Sexp) ([x xs] [c cs] [γ γs])
            `(,x : (,(show-α γ) @ ,(show-?e c))))
        ↦ ,(show-e rng))
       ◃ ,(show-α α))]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-=>i xs cs γs d ρ Γ)
     `(,@(for/list : (Listof Sexp) ([x xs] [c cs] [γ γs])
           `(,x : (,(show-α γ) @ ,(show-?e c))))
       ↦ ,(show-e d))]
    [(-St/C s αs)
     `(,(string->symbol (format "~a/c" (show-struct-info s))) ,@(map show-α αs))]
    [(-μ/C x α) `(μ/C (,x) ,(show-α α))]
    [(-X/C α) `(X: ,(show-α α))]))

(define (show-A [A : -A]) : Sexp
  (match A
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V V) ,(map show-V C))]
    [(? list? Vs) (map show-V Vs)]))

(define (show-WV [WV : -WV]) : (Listof Sexp)
  (match-define (-W V e) WV)
  `(,(show-V V) @ ,(show-?e e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; environment maps variable names to addresses
(define-type -ρ (Map Symbol -α))
(define -ρ⊥ : -ρ (hash))

(: ρ↓ : -ρ (Setof Symbol) → -ρ)
;; Restrict environment's domain to given variable names
(define (ρ↓ ρ xs)
  (cond ; reuse empty collection in special cases
   [(set-empty? xs) -ρ⊥]
   [else (for/fold ([ρ* : -ρ -ρ⊥]) ([x xs])
           (hash-set ρ* x (ρ@ ρ x)))]))

(: ρ+ : -ρ (U -x Symbol) -α → -ρ)
;; Extend environment with new mapping from symbol to address
(define (ρ+ ρ x α)
  (define s (if (-x? x) (-x-name x) x))
  (hash-set ρ s α))

(: ρ++ : -ρ -formals (Listof -α) → -ρ)
;; Extend environment with given parameter and argument lists
(define (ρ++ ρ xs αs)
  (match xs
    [(? list? xs)
     (for/fold ([ρ : -ρ ρ]) ([x xs] [α αs])
       (hash-set ρ x α))]
    [(-varargs init rest)
     (let go ([ρ ρ] [xs xs] [αs αs])
       (match* (xs αs)
         [((cons x xs*) (cons α αs*))
          (go (hash-set ρ x α) xs* αs*)]
         [('() αs)
          (error 'ρ++ "TODO: varargs")]
         [((cons _ _) _)
          (error 'ρ++ "more parameters than arguments")]))]))

(: ρ@ : -ρ (U -x Symbol) → -α)
;; Look up environment for address at given variable
(define (ρ@ ρ x)
  (define s (if (-x? x) (-x-name x) x))
  (hash-ref ρ s))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) (in-hash ρ)])
    `(,x ↦ ,(show-α α))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-data -α
  ;; for top-level definition and contract
  (struct -α.def [id : -id])
  (struct -α.ctc [id : -id])
  ;; for lexical binding
  ;(struct -α.bnd [x : Symbol] [arg : -?e] [inv : -Γ])
  Symbol
  ;; TODO: temp hack
  (struct -α.tmp [v : -e])
  ;; for mutable or opaque field
  (struct -α.fld [id : (U -id #|HACK|# Symbol)] [loc : (Option Integer)] [idx : Integer]))

(: alloc-fields : -struct-info (Option Integer) (Listof -WV) → (Listof -α))
(define (alloc-fields s loc Ws)
  #|FIXME|# (match-define (-struct-info id n _) s)
  (for/list ([W Ws] [i (in-range n)])
    (match-define (-W V _ #|TODO matters?|#) W)
    (-α.fld id loc i)))

(define show-α : (-α → Symbol) (unique-name 'α))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; store maps addresses to values
(define-type -σ (MMap -α -V))
(define -σ⊥ : -σ (hash))
(define-type -Δσ (ΔMap -α -V))

(: σ@ : -σ -α → (Setof -V))
;; Look up the store for all values at given address
(define (σ@ σ α) (hash-ref σ α))

(: σ@₁ : -σ -α → -V)
;; Look up the store for a single value at given address
(define (σ@₁ σ α)
  (define Vs (hash-ref σ α))
  (cond
    [(= 1 (set-count Vs)) (set-first Vs)]
    [else (error 'Internal "expect exactly 1 value at address ~a, given ~a"
                 α (set-count Vs))]))

(: σ@/list : -σ (Listof -α) → (Setof (Listof -V)))
;; Look up store, return every possible list of values
(define (σ@/list σ αs)
  (match αs
    ['() {set (list)}]
    [(cons α βs)
     (define Vss (σ@/list σ βs))
     (for*/set: : (Setof (Listof -V)) ([V (σ@ σ α)] [Vs Vss])
       (cons V Vs))]))

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) (in-hash σ)])
    `(,(show-α α) ↦ ,@(for/list : (Listof Sexp) ([V Vs]) (show-V V)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Summarization table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -Res ([e : -?e] [facts : -es]) #:transparent)
(define -Res⊤ (-Res #f ∅))
(define-type -M (MMap -e -Res))
(define-type -ΔM (ΔMap -e -Res))
(define -M⊥ : -M (hash))

(: M⊔ : -M -e -WVs -es → -M)
;; Update summarization table
(define (M⊔ M e W es)
  (match-define (-W _ ?e) W)
  (⊔ M e (-Res ?e es)))

(define (show-Res [r : -Res]) : (Listof Sexp)
  (match-define (-Res e es) r)
  `(,(show-?e e) : ,@(show-es es)))

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list : (Listof Sexp) ([(e Reses) M])
    `(,(show-e e) ↝⋆ ,@(set-map Reses show-Res))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Operations on satisfiability result
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Satisfiability result
(define-type -R (U '✓ 'X '?))

(: not-R : -R → -R)
;; Negate provability result
(define not-R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

;; Use the first definite result
(define-syntax or-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (match R₁ ['? (or-R R ...)] [ans ans])]))

(define (decide-R [x : Boolean]) : -R (if x '✓ 'X))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Convenience
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -Mt (-St -s-null (list)))
(define -Any/C (-Clo '(x) -tt -ρ⊥ -Γ⊤))
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -● (-W '• #f))
(define -Void/Vs (list (-St -s-void '())))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))

(: -?@ : -?e -?e * → -?e)
;; Smart constructor for application
(define (-?@ f . xs)

  (: access-same-value? : -struct-info (Listof -?e) → (Option -e))
  ;; If given expression list of the form like `(car e); (cdr e)`, return `e`.
  ;; Otherwise just `#f`
  (define (access-same-value? info es)
    (define n (-struct-info-arity info))
    (match es
      [(cons (-@ (-st-ac info₀ 0) (list e₀) _) es*)
       (and (equal? info info₀)
            (for/and : Boolean ([i (in-range 1 n)] [ei es*])
              (match ei
                [(-@ (-st-ac infoⱼ j) (list eⱼ) _)
                 (and (equal? info infoⱼ) (= i j) (equal? e₀ eⱼ))]
                [_ #f]))
            e₀)]
      [_ #f]))
  
  (cond
    [(and f (andmap (inst values -?e) xs))
     (match* (f xs)
       ; (not (not e)) = e
       [('not (list (-not e))) e]
       ; (car (cons e _)) = e
       [((-st-ac s i) (list (-@ (-st-mk s) es _)))
        (list-ref es i)]
       ; (cons (car e) (cdr e)) = e
       [((-st-mk s) es)
        (or (access-same-value? s es)
            (-@ f (cast xs (Listof -e)) -Λ))]
       ; ariths
       [('+ (list-no-order (-b 0) e*)) (assert e* -e?)]
       [('+ (list (-@ '+ (list e₁ e₂) _) e₃))
        (-@ '+ (list e₁ (-@ '+ (list e₂ (assert e₃)) -Λ)) -Λ)]
       [('* (list-no-order (-b 1) e*)) (assert e* -e?)]
       [('* (list (-@ '* (list e₁ e₂) _) e₃))
        (-@ '* (list e₁ (-@ '* (list e₂ (assert e₃)) -Λ)) -Λ)]
       ; default
       [(f xs) (-@ f (cast xs (Listof -e)) -Λ)])]
    [else #f]))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not e)]))

(:* -and/c-split -or/c-split : -?e → (Values -?e -?e))
(define -and/c-split
  (match-lambda
    [(-@ (-st-mk (≡ -s-and/c)) (list c d) _) (values c d)]
    [c (values (-?@ (-st-ac -s-and/c 0) c)
               (-?@ (-st-ac -s-and/c 1) c))]))
(define -or/c-split
  (match-lambda
    [(-@ (-st-mk (≡ -s-or/c)) (list c d) _) (values c d)]
    [c (values (-?@ (-st-ac -s-or/c 0) c)
               (-?@ (-st-ac -s-or/c 1) c))]))
(: -not/c-neg : -?e → -?e)
(define (-not/c-neg c)
  (-?@ (-st-ac -s-not/c 0) c))

(: -struct/c-split : -?e Integer → (Listof -?e))
(define (-struct/c-split c n)
  (match c
    [(-struct/c _ cs _) cs]
    [_
     (define s (-struct-info 'struct/c n ∅)) ; hack
     (for/list : (Listof -?e) ([i (in-range n)])
         (-?@ (-st-ac s i) c))]))

(: -struct-split : -?e -struct-info → (Listof -?e))
(define (-struct-split e s)
  (match e
    [(-@ (-st-mk (≡ s)) es _) es]
    [_ (for/list : (Listof -?e) ([i (in-range (-struct-info-arity s))])
         (-?@ (-st-ac s i) e))]))

(: -?struct/c : -struct-info (Listof -?e) → (Option -struct/c))
(define (-?struct/c s fields)
  (and (andmap (inst values -?e) fields)
       (-struct/c s (cast fields (Listof -e)) #f)))

(: -?->i : (Listof Symbol) (Listof -?e) -?e -> (Option -->i))
(define (-?->i xs cs d)
  (and d (andmap (inst values -?e) cs)
       (-->i (map (inst cons Symbol -e) xs (cast cs (Listof -e))) d #f)))

(: split-values : -?e Integer → (Listof -?e))
;; Split a pure expression `(values e ...)` into `(e ...)`
(define (split-values e n)
  (match e
    [(-@ 'values es _)
     (cond [(= n (length es)) es]
           [else (error 'split-values "cannot split ~a values into ~a" (length es) n)])]
    [(? -e?)
     (cond [(= 1 n) (list e)]
           [else #|hack|#
            (define s (-struct-info 'values n ∅))
            (for/list ([i (in-range n)])
              (-?@ (-st-ac s i) e))])]
    [_ (make-list n #f)]))
