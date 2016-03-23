#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "../utils/set.rkt" "../ast/main.rkt" "definition.rkt")

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

(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) 0))
                                (-@ '+ (list (-x 'x) (-x 'y)) 0))
                (-@ '+ (list (-@ '+ (list (-b 1) (-b 2)) 0) (-x 'y)) 0)))
