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

(: es↓ : (℘ -e) (℘ Var-Name) → (℘ -e))
(define (es↓ es xs)
  (for*/set: : (℘ -e) ([e es]
                       [e* (in-value (e↓ e xs))] #:when e*)
     e*))

(: Γ↓ : -Γ (℘ Var-Name) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)

  (match-define (-Γ φs as γs) Γ)
  (define φs* (es↓ φs xs))
  (define as*
    (for/hasheq : (HashTable Var-Name -e) ([(x e) as] #:when (∋ xs x))
      (values x e)))
  (define γs*
    (for/list : (Listof -γ) ([γ γs])
      (match-define (-γ αₖ bnd blm) γ)
      (-γ αₖ (bnd↓ bnd xs) blm)))
  (-Γ φs* as* γs*))

(: bnd↓ : -binding (℘ Var-Name) → -binding)
(define (bnd↓ bnd fvs)
  (match-define (-binding f xs x->e) bnd)
  (define f* (s↓ f fvs))
  (define x->e*
    (for*/hasheq : (HashTable Var-Name -s) ([(x e) x->e]
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
        [else (e/map (for/hash : Subst ([(x eₓ) X]) (values (-x x) eₓ)) e)]))

(: -Γ-plus-γ : -Γ -γ → -Γ)
(define (-Γ-plus-γ Γ γ)
  (match-define (-Γ φs as γs) Γ)
  (-Γ φs as (cons γ γs)))

(: γ->fargs : -γ → -s)
(define (γ->fargs γ)
  (match-define (-γ _ bnd _) γ)
  (binding->fargs bnd))

(: binding->fargs : -binding → -s)
(define (binding->fargs bnd)
  (match-define (-binding f xs x->e) bnd)
  (define args : (Listof -s) (for/list ([x xs]) (hash-ref x->e x #f)))
  (apply -?@ f args))

(: fvₛ : -s → (℘ Var-Name))
(define (fvₛ s) (if s (fv s) ∅eq))

(: invalidate : -Γ Var-Name → -Γ)
;; Throw away anything known about `x` in `Γ`
(define (invalidate Γ x)
  (match-define (-Γ φs as γs) Γ)
  (define φs*
    (for/set: : (℘ -e) ([φ φs] #:unless (∋ (fv φ) x))
      φ))
  (define as*
    (for/hasheq : (HashTable Var-Name -e) ([(z φ) as]
                                           #:unless (eq? z x)
                                           #:unless (∋ (fv φ) x))
      (values z φ)))
  (define γs*
    (for/list : (Listof -γ) ([γ γs])
      (match-define (-γ αₖ bnd blm) γ)
      (match-define (-binding f xs x->e) bnd)
      (define bnd*
        (let ([f* (if (∋ (fvₛ f) x) #f f)]
              [x->e*
               (for/hasheq : (HashTable Var-Name -s) ([(z φ) x->e]
                                                      #:unless (∋ (fvₛ φ) x))
                 (values z φ))])
          (-binding f* xs x->e*)))
      (-γ αₖ bnd* blm)))
  (-Γ φs* as* γs*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-M-Γ [M : -M] [Γ : -Γ]) : (Values Sexp (Listof Sexp))
  (match-define (-Γ _ _ γs) Γ)
  (values (show-Γ Γ)
          (map (curry show-M-γ M) γs)))

(define (show-M-γ [M : -M] [γ : -γ]) : (Listof Sexp)
  (match-define (-γ αₖ bnd blm) γ)
  (define ΓAs (M@ M αₖ))
  (define ↦ (if blm '↦ₑ '↦ᵥ))
  `(,(show-γ γ) ≡ (,(show-αₖ αₖ) @ ,(show-binding bnd)) ,↦ ,@(set-map ΓAs show-ΓA)))

(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) +ℓ₀))
                                (-@ '+ (list (-x 'x) (-x 'y)) +ℓ₀))
                (-@ '+ (list (-b 1) (-@ '+ (list (-b 2) (-x 'y)) +ℓ₀)) +ℓ₀)))
