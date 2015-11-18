#lang typed/racket/base
(require
 racket/match racket/list racket/set racket/function
 "untyped-macros.rkt" "utils.rkt" "ast.rkt"
 ; for generated code
 racket/math racket/flonum racket/extflonum racket/string
 (for-syntax racket/base racket/match racket/list racket/contract racket/syntax syntax/parse
             "untyped-macros.rkt" "utils.rkt" (prefix-in prims: "prims.rkt") "prim-gen.rkt"))
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
  ;; Structs
  (struct -St [info : -struct-info] [fields : (Listof -α)])
  (struct -St/checked
    [info : -struct-info] [contracts : (Listof (Option -α))] [mon : Mon-Info]
    [unchecked : -α])
  ;; Vectors
  (struct -Vector [fields : (Listof -α)])
  (struct -Vector/checked [contracts : (Listof -α)] [mon : Mon-Info] [unchecked : -α])
  ;; Functions
  (struct -Clo* [xs : -formals] [e : -e] [ρ : -ρ]) ; unescaped closure
  (struct -Clo [xs : -formals] [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -Ar
    [xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)]
    [rng : -e] [env : -ρ] [Γ : -Γ]
    [v : -α] [l³ : Mon-Info])
  ;; Contracts
  ; Treat `and/c`, `or/c` specially to deal with `chaperone?`
  ; But these give rise to more special cases of stack frames
  (struct -And/C [flat? : Boolean] [l : -α] [r : -α])
  (struct -Or/C [flat? : Boolean] [l : -α] [r : -α])
  (struct -Not/C [γ : -α])
  (struct -Vectorof [γ : -α])
  (struct -Vector/C [γs : (Listof -α)])
  (struct -St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α)])
  (struct -=>i
    [xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)]
    [rng : -e] [env : -ρ] [Γ : -Γ])
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

(: C-flat? : -V → Boolean)
;; Check whether value is a flat contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>i?) #f]
    [(or (? -Clo*?) (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [V
     (printf "`C-flat?`: warning: receiving non-contract ~a~n" (show-V V))
     #t]))

;; Pretty-print evaluated value
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
    [(-St/checked s γs _ α)
     `(,(string->symbol (format "~a/wrapped" (show-struct-info s)))
       ,@(for/list : (Listof Symbol) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/checked γs _ α) `(vector/wrapped ,@(map show-α γs) ▹ ,(show-α α))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=>i xs cs γs d ρ Γ)
     `(,@(for/list : (Listof Sexp) ([x xs] [c cs] [γ γs])
           `(,x : (,(show-α γ) @ ,(show-?e c))))
       ↦ ,(show-e d))]
    [(-St/C _ s αs)
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
  (struct -α.fld [id : (U -id #|HACK|# Symbol)] [pos : Integer] [idx : Integer])
  ;; for wrapped mutable struct
  (struct -α.wrp [id : -id] [pos : Integer])
  ;; for vector indices
  (struct -α.vct [pos : Integer] [idx : Integer])
  ;; for inner vector
  (struct -α.inv [pos : Integer]))

(: alloc-fields : -struct-info Integer (Listof -WV) → (Listof -α))
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
(define -integer?/W (-W 'integer? 'integer?))
(define -number?/W (-W 'number? 'number?))
(define -vector?/W (-W 'vector? 'vector?))
(define -procedure?/W (-W 'procedure? 'procedure?))
(define -vector-ref/W (-W 'vector-ref 'vector-ref))
(define -vector-set/W (-W 'vector-set! 'vector-set!))
(define -=/W (-W '= '=))
(define -Vector₀ (-Vector '()))

(define (-=/C [n : Integer])
  (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤))

(define (-not/C [v : -v])
  (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) -Λ)) -Λ) -ρ⊥ -Γ⊤))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))

(begin-for-syntax

  (define/contract (general-primitive-clauses f xs)
    (identifier? identifier? . -> . (listof syntax?))

    (define default-case (datum->syntax f '(default-case)))

    (define/contract (go dec)
      (any/c . -> . (listof syntax?))
      (match dec
        [`(#:pred ,(? symbol? s))
         (go `(,s (any/c . -> . boolean?) #:other-errors))]
        [`(#:pred ,(? symbol? s) (,(? prims:ctc? cs) ...))
         (go `(,s (,@cs . -> . boolean?) #:other-errors))]
        [`(#:batch (,(? symbol? ss) ...) ,(? prims:arr? c) ,_ ...)
         (append-map (λ (s) (go `(,s ,c #:other-errors))) ss)]
        [`(,(? symbol? o) (,cs ... . -> . ,d) ,_ ...)

         (cond
           [(and (andmap prims:base? cs) (prims:base? d))
            
            (define b-ids
              (for/list ([(_ i) (in-indexed cs)])
                (datum->syntax #f (string->symbol (format "x~a" (n-sub i))))))
            
            (define/contract b-pats (listof syntax?)
              (for/list ([b-id b-ids] [c cs])
                (match c
                  [(? symbol? p) #`(-b (? #,c #,b-id))]
                  [`(not/c ,(? symbol? p)) #`(-b (not (? #,c #,b-id)))]
                  [`(and/c ,ps ...)
                   #`(-b (and #,@(map mk-pat ps) #,b-id))]
                  [`(or/c ,ps ...)
                   #`(-b (and (or #,@(map mk-pat ps)) #,b-id))])))
            (list
             #`[(#,o)
                (match #,xs
                  [(list #,@b-pats) (-b (#,o #,@b-ids))]
                  [_ #,default-case])])]
           [else '()])]
        [_ '()]))
    
    (append-map go prims:prims)))

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

  (define (default-case) : -e
    (-@ (assert f) (cast xs (Listof -e)) -Λ))

  (define-syntax (general-primitive-case stx)
    #`(case f
        #,@(general-primitive-clauses #'f #'xs)
        [else (default-case)]))
  
  (cond
    [(and f (andmap (inst values -?e) xs))
     (match f
       ; vector-length
       ['vector-length
        (match xs
          [(list (-@ 'vector xs _)) (-b (length xs))]
          [_ (default-case)])]

       ; (not³ e) = (not e) 
       ['not
        (match xs
          [(list (-not (and e* (-not _)))) e*]
          [_ (default-case)])]
       
       ; (car (cons e _)) = e
       [(-st-ac s i)
        (match xs
          [(list (-@ (-st-mk s) es _)) (list-ref es i)]
          [_ (default-case)])]
       [(-st-ac s i)
        (match-define (list x) xs)
        (cond ; don't build up syntax when reading from mutable states
          [(∋ (-struct-info-mutables s) i) #f]
          [else (-@ f (list (assert x)) -Λ)])]

       ; (cons (car e) (cdr e)) = e
       [(-st-mk s)
        (or (access-same-value? s xs)
            (-@ f (cast xs (Listof -e)) -Λ))]

       ; General case
       [_ (general-primitive-case)])]
    [else #f]))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not e)]))

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
    [(-@ (-st-mk (≡ s)) es _)
     (define mutables (-struct-info-mutables s))
     (for/list ([(e i) (in-indexed es)])
       (if (∋ mutables i) #f e))]
    [_ (for/list : (Listof -?e) ([i (in-range (-struct-info-arity s))])
         (-?@ (-st-ac s i) e))]))

(: -?struct/c : -struct-info (Listof -?e) → (Option -struct/c))
(define (-?struct/c s fields)
  (and (andmap (inst values -?e) fields)
       (-struct/c s (cast fields (Listof -e)) 0)))

(: -?->i : (Listof Symbol) (Listof -?e) -?e -> (Option -->i))
(define (-?->i xs cs d)
  (and d (andmap (inst values -?e) cs)
       (-->i (map (inst cons Symbol -e) xs (cast cs (Listof -e))) d 0)))

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
