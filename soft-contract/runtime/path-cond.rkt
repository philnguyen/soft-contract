#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "definition.rkt"
         "simp.rkt")

(: s↓ : -s (℘ Var-Name) → -s)
;; Restrict symbol to given set of free variables
(define (s↓ s xs)
  (and s (e↓ s xs)))
(: e↓ : -e (℘ Var-Name) → -s)
(define (e↓ e xs)
  (and (⊆ (fv e) xs) e))

(: φs↓ : (℘ -e) (℘ Var-Name) → (℘ -e))
(define (φs↓ φs xs)
  (for*/set: : (℘ -e) ([φ φs] [φ* (in-value (e↓ φ xs))] #:when φ*)
    φ*))

(: Γ↓ : -Γ (℘ Var-Name) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)

  (match-define (-Γ φs as γs) Γ)
  (define φs* (φs↓ φs xs))
  (define as*
    (for/hash : (HashTable Var-Name -e) ([(x e) as] #:when (∋ xs x))
      (values x e)))
  (define γs*
    (for*/set: : (℘ -γ) ([γ γs])
      (match-define (-γ τ bnd blm) γ)
      (-γ τ (bnd↓ bnd xs) blm)))
  (-Γ φs* as* γs*))

(: bnd↓ : -binding (℘ Var-Name) → -binding)
(define (bnd↓ bnd fvs)
  (match-define (-binding f xs x->e) bnd)
  (define f* (s↓ f fvs))
  (define x->e*
    (for*/hash : (HashTable Var-Name -e) ([(x e) x->e]
                                          [e* (in-value (s↓ e fvs))] #:when e*)
      (values x e*)))
  (-binding f* xs x->e*))

(: canonicalize : (U -Γ (HashTable Var-Name -e)) Var-Name → -e)
;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize X x)
  (cond [(-Γ? X) (canonicalize (-Γ-aliases X) x)]
        [else (hash-ref X x (λ () (-x x)))]))

;; Return an expression canonicalizing given expression in terms of lexically farthest possible variable(s)
(: canonicalize-e : (U -Γ (HashTable Var-Name -e)) -e → -e)
(define (canonicalize-e X e)
  (cond [(-Γ? X) (canonicalize-e (-Γ-aliases X) e)]
        [else
         ((e/map (for/hash : (HashTable -e -e) ([(x e-x) X])
                   (values (-x x) e-x)))
          e)]))

(: -Γ-plus-γ : -Γ -γ → -Γ)
(define (-Γ-plus-γ Γ γ)
  (match-define (-Γ φs as γs) Γ)
  (-Γ φs as (set-add γs γ)))

(: -Γ-minus-γ : -Γ -γ → -Γ)
(define (-Γ-minus-γ Γ γ)
  (match-define (-Γ φs as γs) Γ)
  (-Γ φs as (set-remove γs γ)))

(: γ/ : (HashTable -e -e) → -γ → -γ)
(define ((γ/ m) γ)
  (match-define (-γ τ bnd blm) γ)
  (-γ τ ((binding/ m) bnd) blm))

(: binding/ : (HashTable -e -e) → -binding → -binding)
(define ((binding/ m) bnd)
  (match-define (-binding f xs x->e) bnd)
  (define subst (e/map m))
  (define f* (and f (subst f)))
  (define x->e* (map/hash subst x->e))
  (-binding f* xs x->e*))

(: γ->fargs : -γ → -s)
(define (γ->fargs γ)
  (match-define (-γ _ bnd _) γ)
  (binding->fargs bnd))

(: binding->fargs : -binding → -s)
(define (binding->fargs bnd)
  (apply -?@ (-binding-fun bnd) (-binding-args bnd)))

(: fvₛ : -s → (℘ Var-Name))
(define (fvₛ s) (if s (fv s) ∅))

(define (show-M-Γ [M : -M] [Γ : -Γ]) : (Values Sexp (Listof Sexp))
  (match-define (-Γ _ _ γs) Γ)
  (define ts (set-map γs (curry show-M-γ M)))
  (values (show-Γ Γ) ts))

(define (show-M-γ [M : -M] [γ : -γ]) : (Listof Sexp)
  (match-define (-γ τ bnd blm) γ)
  (define As (M@ M τ))
  (define ↦ (if blm '↦ₑ '↦ᵥ))
  `(,(show-γ γ) ≡ (,(show-τ τ) @ ,(show-binding bnd)) ,↦ ,@(set-map As show-A)))

(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) 0))
                                (-@ '+ (list (-x 'x) (-x 'y)) 0))
                (-@ '+ (list (-@ '+ (list (-b 1) (-b 2)) 0) (-x 'y)) 0)))
