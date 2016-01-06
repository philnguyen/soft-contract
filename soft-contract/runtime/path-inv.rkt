#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/set.rkt" "../utils/def.rkt" "../utils/map.rkt" "../utils/untyped-macros.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt")

;; Path invariant represented by expressions known to evaluate to truth
;; independent of mutable states
;; The bindings `(x ≡ e)` are just a way of storing `(equal? x e)`
;; for faster queries
(struct -Γ ([bindings : (Map (U Symbol -id) -e)] [facts : -es]) #:transparent)
(define -Γ⊤ (-Γ (hash) ∅))
(define-type/pred -?e (Option -e))

(: canonicalize : (U -Γ (Map (U Symbol -id) -e)) -e → -e)
;; Rewrite invariant in terms of lexically farthest variables possible
(define (canonicalize Γ+bnds e)
  (define bnds (if (-Γ? Γ+bnds) (-Γ-bindings Γ+bnds) Γ+bnds))
  (define f
    (match-lambda
      [(-x x)        (hash-ref bnds x  #f)]
      [_ #f]))
  ((e/fun f) e))

(: Γ↓ : -Γ (Setof Symbol) → -Γ)
;; Restrict path invariant to given variables
(define (Γ↓ Γ xs)
  (match-define (-Γ bnds facts) Γ)
  (define bnds*
    ; should be the case: x ∈ xs ⇒ FV⟦bnds(e)⟧ ⊆ xs
    (for/hash : (Map (U Symbol -id) -e) ([(x e) bnds] #:when (or (-id? x) (∋ xs x)))
      (values x e)))
  (define facts*
    (for/set: : -es ([e facts] #:when (⊆ (FV e) xs)) e))
  (-Γ bnds* facts*))

(: Γ↓∅ : -Γ → -Γ)
;; Drop all free variables in path-invariant
(define (Γ↓∅ Γ) (Γ↓ Γ ∅))

(: Γ+ : -Γ -?e * → -Γ)
;; Extend path invariant
(define (Γ+ Γ . es)
  (match-define (-Γ bnds facts) Γ)
  (define facts*
    (for/fold ([facts* : -es facts]) ([e es] #:when e)
      (set-add facts* (canonicalize bnds e))))
  (-Γ bnds facts*))

(: Γ-bind : -Γ (U Symbol -id) -?e → -Γ)
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
    (for/hash : (Map (U Symbol -id) -e) ([(z ez) bnds] #:unless (or (equal? z x) (∋ (FV ez) x)))
      (values z ez)))
  (define facts* (for/set: : -es ([e facts] #:unless (∋ (FV e) x)) e))
  (-Γ bnds* facts*))

(: Γ-reset : -Γ Symbol -?e → -Γ)
;; Reset binding for variable `x`
(define (Γ-reset Γ x e)
  (Γ-bind (Γ-invalidate Γ x) x e))

(: FV-Γ : -Γ → (Setof Symbol))
(define (FV-Γ Γ)
  (for/set: : (Setof Symbol) ([x (in-hash-keys (-Γ-bindings Γ))] #:when (symbol? x))
    x))

(: Γ/ : -Γ Symbol -e → -Γ)
(define (Γ/ Γ x e)
  (match-define (-Γ bnds facts) Γ)
  ; if variable is an alias for another expression `eₓ`,
  ; perform substitution in terms of that expression `eₓ`
  (define pt (hash-ref bnds x (λ () (-x x))))
  (define bnds*
    (for/hash : (Map (U Symbol -id) -e) ([(x e₀) bnds])
      (values x (e/ pt e e₀))))
  (define facts*
    (for/set: : -es ([e₀ facts])
      (e/ pt e e₀)))
  (-Γ bnds* facts*))

(: Γ-binds? : -Γ Symbol → Boolean)
;; Check if variable is bound in path invariant
(define (Γ-binds? Γ x)
  (hash-has-key? (-Γ-bindings Γ) x))

(: Γ-has? : -Γ -?e → Boolean)
;; Check if `Γ` readily remembers `e`
(define (Γ-has? Γ e) (∋ (-Γ-facts Γ) e))

(: concretized? : -Γ -?e → (Option -λ))
;; Check whether the given expression has been concretized during execution
(define (concretized? Γ f)
  (for/or : (Option -λ) ([φ (-Γ-facts Γ)])
    (match φ
      [(-@ 'equal? (list (≡ f) (? -λ? lam)) _) lam]
      [_ #f])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-?e [e : -?e]) : Sexp
  (cond [e (show-e e)]
        [else '⊘]))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ bnds facts) Γ)
  `(,@(for/list : (Listof Sexp) ([(x e) bnds])
        (define name
          (match x
            [(-id name _) name]
            [(? symbol? x) x]))
        `(≡ ,name ,(show-e e)))
    ,@(for/list : (Listof Sexp) ([e facts])
        (show-e e))))
