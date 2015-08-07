#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;; Provability result
(define-type -R (U '✓ 'X '?))

;;;;; Restricted expression + fact environments

(define-data -π
  -x
  -prim
  -id ; for top-level reference
  (struct -π@ [f : -π] [xs : (Listof -π)]))
(define-type -π* (Option -π))

(define-type -Γ (Setof -π))
(define -Γ∅ : -Γ ∅)

;; Extend fact environment
(define (Γ+ [Γ : -Γ] [π : -π*]) : -Γ (if π (set-add Γ π) Γ))

(: -π@* : -π* (Listof -π*) → -π*)
;; Smart constructor for restricted application
(define (-π@* f xs)
  (cond
    [(and f (andmap (inst values -π*) xs))
     (match* (f xs)
       [('false? (list (-π@ 'false? (list π)))) π]
       [((-st-ac id n i) (list (-π@ (-st-mk id n) πs)))
        (list-ref πs i)]
       [((-st-mk id n) (list (-π@ (? -st-ac? ac) πs) ...))
        (error "TODO: does this match?")]
       [(f xs) (-π@ f (cast xs (Listof -π)))])]
    [else #f]))

(: FV-π : -π* → (Setof Symbol))
;; Compute free variables in restricted expression
(define (FV-π π*)
  (match π*
    [(-x x) {set x}]
    [(-π@ f xs)
     (for/fold ([sds : (Setof Symbol) (FV-π f)]) ([x xs])
       (∪ sds (FV-π x)))]
    [_ ∅]))

(: FV-Γ  : -Γ → (Setof Symbol))
;; Computes free variables in fact environment
(define (FV-Γ Γ)
  (for/fold ([xs : (Setof Symbol) ∅]) ([π Γ])
    (∪ xs (FV-π π))))

(: π↓ : -π* (Setof Symbol) → -π*)
;; Discard restricted expression if it contains free variables outside given set
(define (π↓ π xs)
  (cond
    [(⊆ (FV-π π) xs) π]
    [else #f]))

(: Γ↓ : -Γ (Setof Symbol) → -Γ)
;; Restrict fact environment's domain to given variable names
(define (Γ↓ Γ xs)
  (for/set: : -Γ ([π Γ] #:when (subset? (FV-π π) xs)) π))

(: π*/ : -π* -π* -π* → -π*)
;; Substitute sub-expression in restricted syntax
(define (π*/ π π₁ π₂)
  (cond
    [π₁
     (match π
       [(or (? -x?) (? -prim?) (? -id?)) (if (equal? π π₁) π₂ π)]
       [(-π@ f xs) (-π@* (π*/ f π₁ π₂)
                         (for/list : (Listof -π*) ([x xs])
                           (π*/ x π₁ π₂)))]
       [#f #f])]
    [else π]))

(: Γ/ : -Γ -π* -π* → -Γ)
;; Substitute sub-expression in fact environment
(define (Γ/ Γ π₁ π₂)
  (cond
    [π₁ (for*/set: : -Γ ([π Γ] [π* (in-value (π*/ π π₁ π₂))] #:when π*)
          π*)]
    [else Γ]))


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

;; `X` paired with restricted expression
(struct (X) -W ([x : X] [π : -π*]) #:transparent)

(define-type -WV (-W -V))
(define-type -WVs (Listof -WV))
(define (WVs->Vs [WVs : -WVs]) : -Vs
  ((inst map -V -WV) -W-x WVs))

;; closure forms
(define-data -E
  (struct -↓ [e : -e] [ρ : -ρ])
  (subset: -Ans
    (-W -blm)
    -WVs))

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

(define-type -ctn (U -e -π -Γ Symbol Integer Boolean))
(define-data -α
  ;; for top-level binding
  (struct -α.top [id : -id])
  ;; for top-level binding'c contract
  (struct -α.ctc [id : -id])
  ;; for other bindings. TODO: decide what i want.
  (struct -α.bnd [ctx : -e] [ctn : (Listof -ctn)]))

(: alloc : -e -ctn * → -α)
;; Allocate address for a run-time binding
(define (alloc ctx . ctns)
  (log-warning "alloc: decide the right type for content")
  (-α.bnd ctx ctns))


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
    [else (error 'Internal "expect exactly 1 value at address ~a, given 2" α)]))


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
