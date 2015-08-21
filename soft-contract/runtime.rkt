#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;; Provability result
(define-type -R (U '✓ 'X '?))

;;;;; Restricted expression + fact environments

(define-type -?e (Option -e))
(define-type -Γ (Setof -e))
(define -Γ∅ : -Γ ∅)

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not (list e))]))

(: Γ+ : -Γ -?e * → -Γ)
;; Extend fact environment
(define (Γ+ Γ . es)
  (for/fold ([Γ* : -Γ Γ]) ([e es] #:when e)
    (set-add Γ e)))

(: -?@ : -?e (Listof -?e) → -?e)
;; Smart constructor for application
(define (-?@ f xs)

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

(: FV-Γ : -Γ → (Setof Symbol))
(define (FV-Γ Γ)
  (for/fold ([xs : (Setof Symbol) ∅]) ([e : -e Γ])
    (set-union xs (FV e))))


;;;;; CLOSURE

;; blessed arrow, struct, and closed lambda
(define-data -V
  'undefined
  -prim
  '•
  (struct -Ar [c : -α] [v : -α] [l³ : Mon-Info])
  (struct -St [tag : -id] [fields : (Listof -α)])
  (struct -Clo [xs : -formals] [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -=>  [dom : (Listof -α)] [rng : -α])
  (struct -=>i [dom : (Listof (Pairof Symbol -α))] [rng : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -St/C [t : -id] [fields : (Listof -α)])
  (struct -μ/C [x : Symbol] [c : -α])
  (struct -X/C [ref : -α]))
(define-type -Vs (Listof -V))

(define-data -A
  -Vs
  (struct -blm [violator : Mon-Party] [origin : Mon-Party] [v : -V] [c : -Vs]))

;; `X` paired with expression
(struct (X) -W ([x : X] [e : -?e]) #:transparent)

(define-type -WV (-W -V))
(define-type -WVs (-W (Listof -V)))

(define (WVs->Vs [WVs : (Listof -WV)]) : -Vs
  ((inst map -V -WV) -W-x WVs))

;; closure forms
(define-data -E
  (struct -↓ [e : -e] [ρ : -ρ])
  (subset: -Ans
    -blm
    -WVs))

(: Γ↓ : -Γ (Setof Symbol) → -Γ)
;; Restrict fact environment's domain to given variable names
(define (Γ↓ Γ xs)
  (for/set: : -Γ ([e Γ] #:when (subset? (FV e) xs)) e))

(: close : -v -ρ -Γ → -V)
;; Create closure from value syntax and environment
(define (close v ρ Γ)
  (match v
    [(-λ xs e)
     (define FV_e (FV e))
     (-Clo xs e (ρ↓ ρ FV_e) (Γ↓ Γ FV_e))]
    [(? -prim? v) v]
    [(? -•ₗ? v) '•]
    [_ (error 'close "Not yet supported: ~a" v)]))

(: -⇓ : -e -ρ → -↓)
;; Close expression with restricted environment
(define (-⇓ e ρ) (-↓ e (ρ↓ ρ (FV e))))


;;;;; ENVIRONMENT

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


;;;;; ADDRESS

(define-data -α
  ;; for top-level definition and contract
  (struct -α.def [id : -id])
  (struct -α.ctc [id : -id])
  ;; for lexical binding
  (struct -α.bnd [x : Symbol] [arg : -?e] [inv : -Γ])
  ;; for immutable concrete field
  (struct -α.val [v : -e])
  ;; for mutable or opaque field
  (struct -α.opq [id : -id] [loc : (Option Integer)] [field : Integer])
  ;; TODO: hack for now
  'undefined)

(: alloc-immut-fields : -st-mk (Listof -WV) → (Listof -α))
(define (alloc-immut-fields k Ws)
  (match-define (-st-mk id n) k)
  (for/list : (Listof -α) ([W Ws] [i (in-range n)])
    (match-define (-W V e) W)
    (cond
      [e (-α.val e)]
      [else (-α.opq id #f #|TODO|# i)])))


;;;;; STORE

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

;;;;; Summarization table
(struct -Res ([e : -?e] [Γ : -Γ]) #:transparent)
(define-type -M (MMap -e -Res))
(define -M⊥ : -M (hash))


;;;;; Convenience

(define -Mt (-St (-id 'null 'Λ) (list)))
(define -Any/C (-Clo '(x) -tt -ρ∅ -Γ∅))
(define -id-cons (-id 'cons 'Λ))
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -● (-W '• #f))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))
