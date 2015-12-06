#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/set.rkt" "../utils/def.rkt" "../utils/map.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt")

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
     (define m
       (for/hash : (HashTable -e -e) ([(x ex) bnds])
         (values (-x x) ex)))
     ((e/map m) e)]))

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
  (define pt (hash-ref bnds x (λ () (-x x))))
  (define bnds*
    (for/hash : (Map Symbol -e) ([(x e₀) bnds])
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-?e [e : -?e]) : Sexp
  (cond [e (show-e e)]
        [else '⊘]))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ bnds facts) Γ)
  `(,@(for/list : (Listof Sexp) ([(x e) bnds])
        `(≡ ,x ,(show-e e)))
    ,@(for/list : (Listof Sexp) ([e facts])
        (show-e e))))
