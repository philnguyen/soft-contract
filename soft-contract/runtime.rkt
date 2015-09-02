#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Path invariant represented by expressions known to evaluate to truth without effects
(define-type -Γ (Setof -e))
(define -Γ∅ : -Γ ∅)
(define-type/pred -?e (Option -e))

(: Γ↓ : -Γ (Setof Symbol) → -Γ)
;; Restrict path invariant to given variables
(define (Γ↓ Γ xs)
  (for/set: : -Γ ([e Γ] #:when (subset? (FV e) xs)) e))

(: Γ+ : -Γ -?e * → -Γ)
(define (Γ+ Γ . es)
  (for/fold ([Γ : -Γ Γ]) ([e es] #:when e)
    (set-add Γ e)))

(: FV-Γ : -Γ → (Setof Symbol))
(define (FV-Γ Γ)
  (for/fold ([xs : (Setof Symbol) ∅]) ([e : -e Γ])
    (set-union xs (FV e))))

(: Γ/ : -Γ Symbol -e → -Γ)
(define (Γ/ Γ x e)
  (for/set: : -Γ ([ei Γ])
    (e/ ei x e)))

(define (show-?e [e : -?e]) : Sexp
  (cond [e (show-e e)]
        [else '⊘]))

(: show-Γ : -Γ → (Listof Sexp))
(define (show-Γ Γ)
  (for/list ([e Γ]) (show-e e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Evaluated closure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; blessed arrow, struct, and closed lambda
(define-data -V
  'undefined
  -prim
  '•
  (struct -Ar [c : -α] [v : -α] [l³ : Mon-Info])
  (struct -St [tag : -id] [fields : (Listof -α)])
  (struct -Clo* [xs : -formals] [e : -e] [ρ : -ρ]) ; unescaped closure
  (struct -Clo [xs : -formals] [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -=>i
    [xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)]
    [rng : -e] [env : -ρ] [Γ : -Γ])
  (struct -St/C [t : -id] [fields : (Listof -α)])
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
    [(-St (-id (or 'and/c 'or/c 'not/c) 'Λ) αs) (C-flat/list? αs)]
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
    [(-Ar γ α _) `(,(show-α γ) ◃ ,(show-α α))]
    [(-St t αs) `(,(-id-name t) ,@(map show-α αs))]
    [(-=>i xs cs γs d ρ Γ)
     `(,@(for/list : (Listof Sexp) ([x xs] [c cs] [γ γs])
           `(,x : (,(show-α γ) @ ,(show-?e c))))
       ↦ ,(show-e d))]
    [(-St/C t αs) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(map show-α αs))]
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
(define -ρ∅ : -ρ (hash))

(: ρ↓ : -ρ (Setof Symbol) → -ρ)
;; Restrict environment's domain to given variable names
(define (ρ↓ ρ xs)
  (cond ; reuse empty collection in special cases
   [(set-empty? xs) -ρ∅]
   [else (for/fold ([ρ* : -ρ -ρ∅]) ([x xs])
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
  (struct -α.bnd [x : Symbol] [arg : -?e] [inv : -Γ])
  ;; for immutable concrete field
  (struct -α.val [v : -e])
  ;; for mutable or opaque field
  (struct -α.opq [id : -id] [loc : (Option Integer)] [field : Integer]))

(: alloc-immut-fields : -st-mk (Listof -WV) → (Listof -α))
(define (alloc-immut-fields k Ws)
  (match-define (-st-mk id n) k)
  (for/list ([W Ws] [i (in-range n)])
    (match-define (-W V e) W)
    (cond
      [e (-α.val e)]
      [else (-α.opq id #f #|TODO|# i)])))

(define show-α : (-α → Symbol) (unique-name 'α))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; store maps addresses to values
(define-type -σ (MMap -α -V))
(define -σ∅ : -σ (hash))

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
;;;;; Convenience
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -Mt (-St (-id 'null 'Λ) (list)))
(define -Any/C (-Clo '(x) -tt -ρ∅ -Γ∅))
(define -id-cons (-id 'cons 'Λ))
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -● (-W '• #f))
(define -Void/Vs (list (-St (-id 'void 'Λ) '())))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))

(: -?@ : -?e -?e * → -?e)
;; Smart constructor for application
(define (-?@ f . xs)

  (: access-same-value? : -id Integer (Listof -?e) → (Option -e))
  (define (access-same-value? id n es)
    (match es
      [(cons (-@ (-st-ac id0 m0 0) (list e0) _) es*)
       (and (equal? id id0)
            (= n m0)
            (for/and : Boolean ([i (in-range 1 n)] [ei es*])
              (match ei
                [(-@ (-st-ac jd mj j) (list ej) _)
                 (and (= n mj) (= i j) (equal? id jd) (equal? e0 ej))]
                [_ #f]))
            e0)]
      [_ #f]))
  
  (cond
    [(and f (andmap (inst values -?e) xs))
     (match* (f xs)
       ; (not (not e)) = e
       [('not (list (-not e))) e]
       ; (car (cons e _)) = e
       [((-st-ac id n i) (list (-@ (-st-mk id n) es _)))
        (list-ref es i)]
       ; (cons (car e) (cdr e)) = e
       [((-st-mk id n) es)
        (or (access-same-value? id n es)
            (-@ f (cast xs (Listof -e)) 'Λ))]
       [(f xs) (-@ f (cast xs (Listof -e)) 'Λ)])]
    [else #f]))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not e)]))

(:* -and/c-split -or/c-split : -?e → (Values -?e -?e))
(define -and/c-split
  (match-lambda
    [(-@ (-st-mk (-id 'and/c 'Λ) 2) (list c d) _) (values c d)]
    [c (values (-?@ (-st-ac (-id 'and/c 'Λ) 2 0) c)
               (-?@ (-st-ac (-id 'and/c 'Λ) 2 1) c))]))
(define -or/c-split
  (match-lambda
    [(-@ (-st-mk (-id 'or/c 'Λ) 2) (list c d) _) (values c d)]
    [c (values (-?@ (-st-ac (-id 'or/c 'Λ) 2 0) c)
               (-?@ (-st-ac (-id 'or/c 'Λ) 2 1) c))]))
(: -not/c-neg : -?e → -?e)
(define (-not/c-neg c) (-?@ (-st-ac (-id 'not/c 'Λ) 1 0) c))

(: -struct/c-split : -?e Integer → (Listof -?e))
(define (-struct/c-split c n)
  (match c
    [(-struct/c _ cs) cs]
    [_ (for/list : (Listof -?e) ([i (in-range n)])
         (-?@ (-st-ac (-id 'struct/c 'Λ) n i) c))]))

(: -struct-split : -?e -id Integer → (Listof -?e))
(define (-struct-split e id n)
  (match e
    [(-@ (-st-mk id n) es _) es]
    [_ (for/list : (Listof -?e) ([i (in-range n)])
         (-?@ (-st-ac id n i) e))]))

(: -?struct/c : -id (Listof -?e) → (Option -struct/c))
(define (-?struct/c id fields)
  (and (andmap (inst values -?e) fields)
       (-struct/c id (cast fields (Listof -e)))))

(: -?->i : (Listof Symbol) (Listof -?e) -?e -> (Option -->i))
(define (-?->i xs cs d)
  (and d (andmap (inst values -?e) cs)
       (-->i (map (inst cons Symbol -e) xs (cast cs (Listof -e))) d)))

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
            (for/list ([i (in-range n)])
              (-?@ (-st-ac (-id 'values 'Λ) n i) e))])]
    [_ (make-list n #f)]))
