#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;; Provability result
(define-type -R (U '✓ 'X '?))

;;;;; Generics
(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (Setof Y)]) (set-add ys y)) (inst set Y)))

;;;;; Pure syntax + fact environments

(define-data -π
  -x
  -prim
  -id
  (struct -π@ [f : -π] [xs : (Listof -π)]))
(define-type -π* (Option -π))

(define-type -Γ (Setof -π))
(define -Γ∅ : -Γ ∅)

(: Γ+ : -Γ -π* → -Γ)
(define (Γ+ Γ π) (if π (set-add Γ π) Γ))

(: -π@* : -π* (Listof -π*) → -π*)
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

(: FV-π : -π* → (Setof Integer))
;; Compute free variables in restricted expression
(define (FV-π π*)
  (match π*
    [(-x sd) {set sd}]
    [(-π@ f xs)
     (for/fold ([sds : (Setof Integer) (FV-π f)]) ([x xs])
       (∪ sds (FV-π x)))]
    [_ ∅]))

(: FV-Γ  : -Γ → (Setof Integer))
;; Computes free variables in fact environment
(define (FV-Γ Γ)
  (for/fold ([xs : (Setof Integer) ∅]) ([π Γ])
    (∪ xs (FV-π π))))

(: restrict-Γ : -Γ (Setof Integer) → -Γ)
;; Restrict fact environment's domain to given static distances
(define (restrict-Γ Γ sds)
  (for/set: : -Γ ([π Γ] #:when (subset? (FV-π π) sds)) π))

;;;;; CLOSURE

;; closure forms
(define-data -E
  (struct -↓ [e : -expr] [ρ : -ρ])
  (subset: -A
    (struct -blm [violator : Mon-Party] [origin : Mon-Party] [v : -V] [c : -V])
    (struct -Ws [ws : (Listof -W)])))

(struct -W ([V : -V] [π : -π*]) #:transparent)

;; blessed arrow, struct, and closed lambda
(define-data -V
  -prim
  '•
  (struct -Ar [c : -α] [v : -α] [l³ : Mon-Info])
  (struct -St [tag : -id] [fields : (Listof -α)])
  (struct -λ↓ [f : -λ] [ρ : -ρ] [Γ : -Γ])
  (struct -λ/C [c : (Listof -α)] [e : -expr] [ρ : -ρ] [Γ : -Γ] [v? : Boolean])
  (struct -St/C [t : -id] [fields : (Listof -α)])
  (struct -μ/C [x : Symbol] [c : -α])
  (struct -X/C [ref : -α]))

(define-match-expander -Ws*
  (syntax-rules () [(_ W ...) (-Ws (list W ...))])
  (syntax-rules () [(_ W ...) (-Ws (list W ...))]))

(: close : -v -ρ -Γ → -V)
(define (close v ρ Γ)
  (cond
    [(-λ? v)
     (define xs (FV v))
     (-λ↓ v (restrict-ρ ρ xs) (restrict-Γ Γ xs))]
    [(-prim? v) v]
    [(-•ₗ? v) '•]
    [else (error 'close "Not yet supported: ~a" v)]))


;;;;; ENVIRONMENT

;; environment maps static distances (HACK: or symbols) to values
(struct -ρ ([map : (Map Integer -α)] [len : Integer]) #:transparent)
(define -ρ∅ (-ρ (hash) 0))

(: restrict-ρ : -ρ (Setof Integer) → -ρ)
;; Restrict environment's domain to given static distances
(define (restrict-ρ ρ sds)
  (cond ; reuse empty collection in special cases
   [(set-empty? sds) -ρ∅]
   [else
    (define m∅ (-ρ-map -ρ∅))
    (match-define (-ρ m l) ρ)
    (define m′
      (for/fold ([acc : (Map Integer -α) m∅]) ([sd sds])
        (define i (- l sd 1))
        (hash-set acc i (hash-ref m i))))
    (-ρ m′ l)]))

(: ρ+ : -ρ -α → -ρ)
(define (ρ+ ρ α)
  (match-define (-ρ m l) ρ)
  (-ρ (hash-set m l α) (+ 1 l)))

(: ρ++ : ([-ρ (Listof -α)] [(U Boolean Integer)] . ->* . -ρ))
(define (ρ++ ρ αs [var? #f])
  (match var?
    [#f (for/fold ([ρi ρ]) ([α αs]) (ρ+ ρi α))]
    [_ (error 'ρ++ "TODO: var args")]
    #|
    [0 (ρ+ ρ (foldr (λ ([Vi : -V] [Vr : -V])
                      (.// (-St -id-cons (list Vi Vr)) ∅))
                    MT V*))]
    [(? integer? n) (ρ++ (ρ+ ρ (car V*)) (cdr V*) (- n 1))]
    |#))

(: ρ-upd : -ρ Integer (Listof -α) → -ρ)
(define (ρ-upd ρ offset αs)
  (match-define (-ρ m l) ρ)
  (define i₀ (- l offset (length αs)))
  (-ρ
   (for/fold ([acc : (Map Integer -α) m]) ([α αs] [δ (in-naturals)])
     (hash-set acc (+ i₀ δ) α))
   l))

(: ρ@ : -ρ (U -x Integer) → -α)
(define (ρ@ ρ x)
  (match-define (-ρ m l) ρ)
  (hash-ref m (- l (if (-x? x) (-x-sd x) x) 1)))

(: ρ-set : -ρ (U -x Integer) -α → -ρ)
(define (ρ-set ρ x α)
  (match-define (-ρ m l) ρ)
  (define sd (match x [(-x sd) sd] [(? integer? sd) sd]))
  (-ρ (hash-set m (- l sd 1) α) l))

(: ρ∋ : -ρ (U -x Integer) → Boolean)
(define (ρ∋ ρ x)
  (match-define (-ρ m l) ρ)
  (define sd (if (-x? x) (-x-sd x) x))
  (hash-has-key? m (- l sd 1)))

;;;;; STORE

(struct -α ([binder : -expr]) #:transparent)
(struct -α-cnc -α ([arg : -expr]) #:transparent)
(struct -α-opq -α ([stx : -π*] [facts : -Γ]) #:transparent)

;; store maps addresses to values
(define-type -σ (MMap -α -V))
(define σ∅ : -σ (hash))

(: σ@ : -σ -α → (Setof -V))
(define (σ@ σ α) (hash-ref σ α))

;; Allocate address for a run-time binding
(: alloc : -expr -W -Γ → -α)
(define (alloc binder W Γ)
  (error 'alloc "TODO"))


;;;;; Convenience

(define -Mt (-St (-id 'null 'Λ) (list)))
(define -Any/C (-λ↓ -any/c -ρ∅ -Γ∅))
(define -id-cons (-id 'cons 'Λ))
(define -True/Vs  (list (-b #t)))
(define -False/Vs (list (-b #f)))

(define-type -AΓs (U (Pairof (Listof -V) -Γ) (Setof (Pairof (Listof -V) -Γ))))
