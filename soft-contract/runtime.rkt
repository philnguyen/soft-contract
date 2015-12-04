#lang typed/racket/base
(require
 racket/match racket/bool racket/list racket/set racket/function
 "untyped-utils.rkt" "utils.rkt" "ast.rkt"
 ; for generated code
 racket/math racket/flonum racket/extflonum racket/string
 (for-syntax
  racket/base racket/set racket/function racket/match racket/list racket/contract
  racket/syntax syntax/parse
  "untyped-utils.rkt" "utils.rkt" (prefix-in prims: "prims.rkt") "prim-gen.rkt"))
(require/typed redex/reduction-semantics
  [variable-not-in (Any Symbol → Symbol)])
(require/typed "prims.rkt"
  [(prims prims:prims) (Listof Any)])
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
  (struct -●)
  ;; Structs
  (struct -St [info : -struct-info] [fields : (Listof -α.fld)])
  (struct -St/checked
    [info : -struct-info] [contracts : (Listof (Option -α))] [mon : Mon-Info]
    [unchecked : -α.wrp])
  ;; Vectors
  (struct -Vector [fields : (Listof -α.vct)])
  (struct -Vector/checked [contracts : (Listof -α)] [mon : Mon-Info] [unchecked : -α.inv])
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
  (struct -And/C [flat? : Boolean] [l : -α.and/c-l] [r : -α.and/c-r])
  (struct -Or/C [flat? : Boolean] [l : -α.or/c-l] [r : -α.or/c-r])
  (struct -Not/C [γ : -α.not/c])
  (struct -Vectorof [γ : -α.vectorof])
  (struct -Vector/C [γs : (Listof -α.vector/c)])
  (struct -St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α.struct/c)])
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
    [(? -•?) -●/V]
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
;; Check whether contract is flat, assuming it's already a contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>i?) #f]
    [(or (? -Clo*?) (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

;; Pretty-print evaluated value
(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-●) '●]
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
  (struct -α.fld [id : -id] [pos : Integer] [idx : Integer])

  ;; for wrapped mutable struct
  (struct -α.wrp [id : -id] [pos : Integer])

  ;; for vector indices
  (struct -α.vct [pos : Integer] [idx : Integer])

  ;; for inner vector
  (struct -α.inv [pos : Integer])

  ;; for contract components
  (struct -α.and/c-l [pos : Integer])
  (struct -α.and/c-r [pos : Integer])
  (struct -α.or/c-l [pos : Integer])
  (struct -α.or/c-r [pos : Integer])
  (struct -α.not/c [pos : Integer])
  (struct -α.vector/c [pos : Integer] [idx : Integer])
  (struct -α.vectorof [pos : Integer])
  (struct -α.struct/c [info : -struct-info] [pos : Integer] [idx : Integer])
  )

(: alloc-fields : -struct-info Integer (Listof -WV) → (Listof -α.fld))
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

;; Take the first definite result
(define-syntax first-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (match R₁ ['? (first-R R ...)] [ans ans])]))

(define (decide-R [x : Boolean]) : -R (if x '✓ 'X))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Operations on procedure arities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Representation of arity in the meta-language to make it easier to manipulate
;; in proof rules.
;; In the object language, it's just Racket's numbers and lists.
(define-data -Arity
  (subset: -Simple-Arity
    Integer
    (struct -Arity-At-Least [val : Integer]))
  (Listof -Simple-Arity))

(: -arity-includes? : -Arity -Arity → Boolean)
;; Check if arity `ar₁` subsumes `ar₂`
(define (-arity-includes? ar₁ ar₂)

  (define (-arity-supports-number? [ar : -Arity] [n : Integer]) : Boolean
    (match ar
      [(? exact-integer? m) (= m n)]
      [(-Arity-At-Least m) (<= m n)]
      [(? list? ars) (for/or ([ari ars]) (-arity-supports-number? ari n))]))

  (define (-arity-supports-at-least? [ar : -Arity] [n : Integer]) : Boolean
    (match ar
      [(? exact-integer?) #f]
      [(-Arity-At-Least m) (<= m n)]
      [(? list? ars)
       (define min-at-least
         (for/fold ([min-at-least : (Option Integer) #f])
                   ([ari ars])
           (match ari
             [(? exact-integer?) min-at-least]
             [(-Arity-At-Least m)
              (cond [min-at-least (min min-at-least m)]
                    [else m])])))
       (and min-at-least
            (for/and ([i (in-range n min-at-least)])
              (-arity-supports-number? ar i)))]))
  
  (match ar₂
    [(? exact-integer? n) (-arity-supports-number? ar₁ n)]
    [(-Arity-At-Least n) (-arity-supports-at-least? ar₁ n)]
    [(? list? ars₂) (for/and ([ari ars₂]) (-arity-includes? ar₁ ari))]))

(: -procedure-arity : -V → (Option -Arity))
;; Return given value's arity
(define -procedure-arity
  (let ()
    
    (define (-formals-arity [xs : -formals]) : -Arity
      (cond
        [(-varargs? xs) (-Arity-At-Least (length (-varargs-init xs)))]
        [else (length xs)]))

    (define arity-table
      (for/fold ([m : (HashTable Symbol -Arity) (hasheq)]) ([dec prims:prims])
        (match dec
          [`(#:pred ,(? symbol? s)) (hash-set m s 1)]
          [`(#:pred ,(? symbol? s) (,xs ...)) (hash-set m s (length xs))]
          [`(#:batch (,ss ...) (,xs ... . -> . ,_) ,_ ...)
           (define n (length xs))
           (for/fold ([m : (HashTable Symbol -Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(#:batch (,ss ...) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (define n (-Arity-At-Least (length (assert xs list?))))
           (for/fold ([m : (HashTable Symbol -Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(,(? symbol? s) (,xs ... . -> . ,_) ,_ ...)
           (hash-set m s (length xs))]
          [`(,(? symbol? s) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (hash-set m s (-Arity-At-Least (length (assert xs list?))))]
          [_ m])))

    (match-lambda
      [(or (-Clo xs _ _ _) (-Clo* xs _ _)) (-formals-arity (assert xs))]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?)) 1]
      [(-Ar xs _ _ _ _ _ _ _) (length xs)]
      [(? -st-p?) 1]
      [(-st-mk (-struct-info _ n _)) n]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? s) (hash-ref arity-table s)]
      [(-●) #f]
      [V (error '-procedure-arity "called on a non-procedure ~a" (show-V V))])))

(module+ test
  (require typed/rackunit)
  (check-true (-arity-includes? 1 1) "1-1")
  (check-true (-arity-includes? (list 1) 1) "(1)-1")
  (check-true (-arity-includes? 1 (list 1)) "1-(1)")
  (check-false (-arity-includes? 1 (-Arity-At-Least 1)) "1-≥1")
  (check-true (-arity-includes? (-Arity-At-Least 1) 1) "≥1-1")
  (check-true (-arity-includes? (-Arity-At-Least 1) (list 1 (-Arity-At-Least 2))) "≥1-1")
  (check-true (-arity-includes? (list 1 (-Arity-At-Least 2)) (-Arity-At-Least 1))
              "(1,≥2)-≥1")
  (check-true (-arity-includes? (-Arity-At-Least 1) (list 1 (-Arity-At-Least 3)))
              "≥1-(1,≥3)")
  (check-false (-arity-includes? (list 1 (-Arity-At-Least 3)) (-Arity-At-Least 1))
               "(1,≥3)-≥1")
  (check-true (-arity-includes? (list 0 1 2 (-Arity-At-Least 3))
                                (list (-Arity-At-Least 0)))
              "(0,1,2,≥3)-≥0")
  (check-true (-arity-includes? (list (-Arity-At-Least 0))
                                (list 0 1 2 (-Arity-At-Least 3)))
              "(≥0)-(0,1,2,≥3)")
  (check-false (-arity-includes? (list 0 2 (-Arity-At-Least 3))
                                 (list (-Arity-At-Least 0)))
               "(0,2,≥3)-(≥0)")
  (check-true (-arity-includes? (list (-Arity-At-Least 0))
                                (list 0 2 (-Arity-At-Least 3)))
              "(≥0)-(0,2,≥3)"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Convenience
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -Null -null)
(define -Any/C (-Clo '(x) -tt -ρ⊥ -Γ⊤))
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -●/V (-●))
(define -Void/Vs (list (-b (void))))
(define -integer?/W (-W 'integer? 'integer?))
(define -number?/W (-W 'number? 'number?))
(define -vector?/W (-W 'vector? 'vector?))
(define -procedure?/W (-W 'procedure? 'procedure?))
(define -vector-ref/W (-W 'vector-ref 'vector-ref))
(define -vector-set/W (-W 'vector-set! 'vector-set!))
(define -arity-includes?/W (-W 'arity-includes? 'arity-includes?))
(define -=/W (-W '= '=))
(define -contract-first-order-passes?/W
  (-W 'contract-first-order-passes? 'contract-first-order-passes?))
(define -Vector₀ (-Vector '()))

(define (-=/C [n : Integer])
  (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤))

(define (-not/C [v : -v])
  (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) -Λ)) -Λ) -ρ⊥ -Γ⊤))

(define (-Arity-Includes/C [n : Integer])
  (-Clo '(x) (-@ 'arity-includes? (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))

;; Helper syntax definition(s) for `-?@`
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
        [`(,(and (? symbol?) (not (? ignore-for-now?)) o) (,cs ... . -> . ,d) ,_ ...)

         (cond
           [(or (prims:base? o) (and (andmap prims:base? cs) (prims:base? d)))
            
            (define/contract b-syms (listof symbol?)
              (build-list (length cs) (λ (i) (string->symbol (format "x~a" (n-sub i))))))
            (define/contract b-ids (listof identifier?) (map (curry datum->syntax f) b-syms))
            (define b-pats (for/list ([b-id b-ids]) #`(-b #,b-id)))
            (define b-conds (datum->syntax f (-sexp-and (map mk-cond b-syms cs))))

            (list
             #`[(#,o)
                (match #,xs
                  [(list #,@b-pats) #:when #,b-conds (-b (#,o #,@b-ids))]
                  #,@(cond
                       [(hash-ref prims:left-ids o #f) =>
                        (λ (lid) (list #`[(list (-b #,lid) e) e]))]
                       [else '()])
                  #,@(cond
                       [(hash-ref prims:right-ids o #f) =>
                        (λ (rid) (list #`[(list e (-b #,rid)) e]))]
                       [else '()])
                  #,@(cond
                       [(∋ prims:assocs o)
                        (list #`[(list (-@ '#,o (list e₁ e₂) _) e₃)
                                 (-?@ '#,o e₁ (-?@ '#,o e₂ e₃))])]
                       [else '()])
                  [_ #,default-case])])]
           [else '()])]
        [_ '()]))
    
    (define ans (append-map go prims:prims))
    ;(printf "~a~n" (pretty (map syntax->datum ans)))
    ans))

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
       ['any/c -tt]
       ['none/c -ff]
       ['void (-b (void))]

       ; vector-length
       ['vector-length
        (match xs
          [(list (-@ 'vector xs _)) (-b (length xs))]
          [_ (default-case)])]

       ; (not³ e) = (not e) 
       ['not
        (match xs
          [(list (-not (and e* (-not _)))) e*]
          [(list (-not (-b x))) (-b (not (not x)))]
          [(list (-b x)) (-b (not x))]
          [_ (default-case)])]
       ['not/c
        (match xs
          [(list (-@ 'not/c (list (and e* (-@ 'not/c _ _))) _)) e*]
          [_ (default-case)])]
       [(-@ 'not/c (list f) _)
        (match xs
          [(list x) (-?@ 'not (-?@ f x))]
          [_ (default-case)])]

       ; TODO: handle `equal?` generally
       ['equal?
        (match xs
          [(list (-b b₁) (-b b₂)) (if (equal? b₁ b₂) -tt -ff)]
          [(list x x) -tt]
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
(module+ test
  (require typed/rackunit)
  (check-equal? (-?@ 'not (-?@ 'not (-?@ 'not (-x 'x)))) (-?@ 'not (-x 'x)))
  (check-equal? (-?@ -car (-?@ -cons (-b 1) (-x 'x))) (-b 1))
  (check-equal? (-?@ '+ (-x 'x) (-b 0)) (-x 'x))
  (check-equal? (-?@ '+ (-b 0) (-x 'x)) (-x 'x))
  (check-equal? (-?@ '* (-?@ '* (-x 'x) (-x 'y)) (-x 'z))
                (-?@ '* (-x 'x) (-?@ '* (-x 'y) (-x 'z))))
  (let ([e (assert (-?@ '+ (-x 'x) (-x 'y)))])
    (check-equal? (-?@ -cons (-?@ -car e) (-?@ -cdr e)) e)
    (check-equal? (-?@ -cons (-?@ -cdr e) (-?@ -car e))
                  (-@ -cons (list (-@ -cdr (list e) -Λ) (-@ -car (list e) -Λ)) -Λ))))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not e)]))

(: -struct/c-split : -?e Integer → (Listof -?e))
(define (-struct/c-split c n)
  (match c
    [(-struct/c _ cs _) cs]
    [_ (make-list n #f)
     #;(define s (-struct-info 'struct/c n ∅)) ; hack
     #;(for/list : (Listof -?e) ([i (in-range n)])
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

(: -app-split : -?e -o Integer → (Listof -?e))
(define (-app-split e o n)
  (match e
    [(-@ (≡ o) es _) es]
    [_ (make-list n #f)]))

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
