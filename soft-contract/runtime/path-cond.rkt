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

(: φ↓ : -?φ (℘ Var-Name) → -?φ)
(define (φ↓ φ xs) (and φ (e↓ (φ->e φ) xs) φ))

(: φs↓ : (℘ -φ) (℘ Var-Name) → (℘ -φ))
(define (φs↓ φs xs)
  (for*/seteq: : (℘ -φ) ([φ φs]
                         [φ* (in-value (φ↓ φ xs))] #:when φ*)
     φ*))

(: Γ↓ : -Γ (℘ Var-Name) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)

  (match-define (-Γ φs as γs) Γ)
  (define φs* (φs↓ φs xs))
  (define as*
    (for/hasheq : (HashTable Var-Name -φ) ([(x φ) as] #:when (∋ xs x))
      (values x φ)))
  (define γs*
    (for/list : (Listof -γ) ([γ γs])
      (match-define (-γ αₖ bnd blm) γ)
      (-γ αₖ (bnd↓ bnd xs) blm)))
  (-Γ φs* as* γs*))

(: bnd↓ : -binding (℘ Var-Name) → -binding)
(define (bnd↓ bnd fvs)
  (match-define (-binding f xs x->φ) bnd)
  (define f* (φ↓ f fvs))
  (define x->φ*
    (for*/hash : (HashTable Var-Name -φ) ([(x φ) x->φ]
                                          [φ* (in-value (φ↓ φ fvs))] #:when φ*)
      (values x φ*)))
  (-binding f* xs x->φ*))

(: canonicalize : (U -Γ (HashTable Var-Name -φ)) Var-Name → -e)
;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize X x)
  (cond [(-Γ? X) (canonicalize (-Γ-aliases X) x)]
        [(hash-ref X x #f) => φ->e]
        [else (-x x)]))

;; Return an expression canonicalizing given expression in terms of lexically farthest possible variable(s)
(: canonicalize-e : (U -Γ (HashTable Var-Name -φ)) -e → -e)
(define (canonicalize-e X e)
  (cond [(-Γ? X) (canonicalize-e (-Γ-aliases X) e)]
        [else
         ((e->φ e)
          (for/hasheq : (HashTable -φ -φ) ([(x φₓ) X])
            (values (e->φ (-x x)) φₓ)))]))

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
  (match-define (-binding φₕ xs x->φ) bnd)
  (define f (and φₕ (φ->e φₕ)))
  (define args : (Listof -s)
    (for/list ([x xs])
      (cond [(hash-ref x->φ x #f) => φ->e]
            [else #f])))
  (apply -?@ f args))

(: fvₛ : -s → (℘ Var-Name))
(define (fvₛ s) (if s (fv s) ∅eq))

(: invalidate : -Γ Var-Name → -Γ)
;; Throw away anything known about `x` in `Γ`
(define (invalidate Γ x)
  (match-define (-Γ φs as γs) Γ)
  (define φs*
    (for/seteq: : (℘ -φ) ([φ φs] #:unless (∋ (fv-φ φ) x))
      φ))
  (define as*
    (for/hasheq : (HashTable Var-Name -φ) ([(z φ) as]
                                           #:unless (eq? z x)
                                           #:unless (∋ (fv-φ φ) x))
      (values z φ)))
  (define γs*
    (for/list : (Listof -γ) ([γ γs])
      (match-define (-γ αₖ bnd blm) γ)
      (match-define (-binding f xs x->φ) bnd)
      (define bnd*
        (let ([f* (if (∋ (fv-φ f) x) #f f)]
              [x->φ*
               (for/hasheq : (HashTable Var-Name -φ) ([(z φ) x->φ]
                                                     #:unless (∋ (fv-φ φ) x))
                 (values z φ))])
          (-binding f* xs x->φ*)))
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
  (check-equal? (canonicalize-e (hash 'x (e->φ (-@ '+ (list (-b 1) (-b 2)) +ℓ₀)))
                                (-@ '+ (list (-x 'x) (-x 'y)) +ℓ₀))
                (-@ '+ (list (-b 1) (-@ '+ (list (-b 2) (-x 'y)) +ℓ₀)) +ℓ₀)))
