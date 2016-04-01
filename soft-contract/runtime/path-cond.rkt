#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/set.rkt"
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

(: Γ↓ : -Γ (℘ Var-Name) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)

  (match-define (-Γ φs as γs) Γ)
  (define φs*
    (for*/set: : (℘ -e) ([φ φs] [φ* (in-value (e↓ φ xs))] #:when φ*)
      φ*))
  (define as*
    (for/hash : (HashTable Var-Name -e) ([(x e) as] #:when (∋ xs x))
      (values x e)))
  (define γs*
    (for*/set: : (℘ -γ) ([γ γs]
                         #:when (s↓ (-γ-fun γ) xs)
                         #:when
                         (for/and : Boolean ([p (-γ-param->arg γ)])
                           (and (s↓ (cdr p) xs) #t))) ; force boolean :(
      γ))
  (-Γ φs* as* γs*))

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

(: Γ/ : (HashTable -e -e) -Γ → -Γ)
;; Substitute free occurrences of `x` with `e` in path condition  
(define (Γ/ m Γ)
  (match-define (-Γ φs as γs) Γ)
  (define subst (e/map m))
  (define φs* (map/set subst φs))
  (define as*
    (for/hash : (HashTable Var-Name -e) ([(x e) as])
      (values x (subst e))))
  (define γs* (map/set (γ/ m) γs))
  (-Γ φs* as* γs*))

(: γ/ : (HashTable -e -e) → -γ → -γ)
(define ((γ/ m) γ)
  (match-define (-γ τ sₕ bnds blm) γ)
  (define subst (e/map m))
  (define bnds* : (Listof (Pairof Var-Name -s))
    (for/list ([bnd bnds])
      (match-define (cons x s) bnd)
      (cons x (and s (subst s)))))
  (define sₕ* (and sₕ (subst sₕ)))
  (-γ τ sₕ* bnds* blm))

(: γ->fargs : -γ → -s)
(define (γ->fargs γ)
  (match-define (-γ _ f bnds _) γ)
  (fbnds->fargs f bnds))

(: fbnds->fargs : -s (Listof (Pairof Var-Name -s)) → -s)
(define (fbnds->fargs f bnds)
  (define args (map (inst cdr Var-Name -s) bnds))
  (apply -?@ f args))

(: fvₛ : -s → (℘ Var-Name))
(define (fvₛ s) (if s (fv s) ∅))


(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) 0))
                                (-@ '+ (list (-x 'x) (-x 'y)) 0))
                (-@ '+ (list (-@ '+ (list (-b 1) (-b 2)) 0) (-x 'y)) 0)))
