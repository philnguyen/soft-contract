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
      (match-define (-γ αₖ blm sₕ sₓs) γ)
      (-γ αₖ blm (s↓ sₕ xs) (for/list : (Listof -s) ([sₓ sₓs]) (s↓ sₓ xs)))))
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
        [else (e/map (for/hash : Subst ([(x eₓ) X]) (values (-x x) eₓ)) e)]))

(: -Γ-plus-γ : -Γ -γ → -Γ)
(define (-Γ-plus-γ Γ γ)
  (match-define (-Γ φs as γs) Γ)
  (-Γ φs as (cons γ γs)))

(: γ->fargs : -γ → -s)
(define (γ->fargs γ)
  (match-define (-γ _ _ sₕ sₓs) γ)
  (apply -?@ sₕ sₓs))

(: fvₛ : -s → (℘ Var-Name))
(define (fvₛ s) (if s (fv s) ∅eq))

(: invalidate : -Γ Var-Name → -Γ)
;; Throw away anything known about `x` in `Γ`
(define (invalidate Γ x)
  (with-debugging/off
    ((Γ*)
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
         (match-define (-γ αₖ blm sₕ sₓs) γ)
         (define sₕ* (and (not (∋ (fvₛ sₕ) x)) sₕ))
         (define sₓs* : (Listof -s)
           (for/list ([sₓ sₓs])
             (and (not (∋ (fvₛ sₓ) x)) sₓ)))
         (-γ αₖ blm sₕ* sₓs*)))
     (-Γ φs* as* γs*))
    (printf "invalidate ~a:~n- before: ~a~n- after: ~a~n~n"
            (show-Var-Name x) (show-Γ Γ) (show-Γ Γ*))))

(: predicates-of : (U -Γ (℘ -e)) -s → (℘ -e))
;; Extract type-like contracts on given symbol
(define (predicates-of Γ s)
  (cond
    [(-Γ? Γ) (predicates-of (-Γ-facts Γ) s)]
    [else
     (for/fold ([ps : (℘ -e) ∅]) ([φ Γ])
       (match φ
         ;; unary
         [(-@ (? -o? o) (list (== s)) _)
          (set-add ps o)]
         ;; binary
         [(-@ (? -o? o) (list (== s) (and v (? -v?) (? closed?))) _)
          (set-add ps (-λ '(𝒙) (-@ o (list (-x '𝒙) v) +ℓ₀)))]
         [(-@ (? -o? o) (list (and v (? -v?) (? closed?)) (== s)) _)
          (set-add ps (-λ '(𝒙) (-@ o (list v (-x '𝒙)) +ℓ₀)))]
         ;; negate unary
         [(-@ 'not (list (-@ (? -o? o) (list (== s)) _)) _)
          (set-add ps (-@ 'not/c (list o) +ℓ₀))]
         ;; negate binary
         [(-@ 'not (list (-@ (? -o? o) (list (== s) (and v (? -v?) (? closed?))) _)) _)
          (set-add ps (-λ '(𝒙) (-@/simp 'not (-@/simp o (-x '𝒙) v))))]
         [(-@ 'not (list (-@ (? -o? o) (list (and v (? -v?) (? closed?)) (== s)) _)) _)
          (set-add ps (-λ '(𝒙) (-@/simp 'not (-@/simp o v (-x '𝒙)))))]
         [_ ps]))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-M-Γ [M : -M] [Γ : -Γ]) : (Values Sexp (Listof Sexp))
  (match-define (-Γ _ _ γs) Γ)
  (values (show-Γ Γ)
          (map (curry show-M-γ M) γs)))

(define (show-M-γ [M : -M] [γ : -γ]) : (Listof Sexp)
  (match-define (-γ αₖ blm sₕ sₓs) γ)
  (define ΓAs (M@ M αₖ))
  (define ↦ (if blm '↦ₑ '↦ᵥ))
  `(,(show-γ γ)
    ≡
    (,(show-αₖ αₖ) @ (,(show-s sₕ) ,@(map show-s sₓs)))
    ,↦ ,@(set-map ΓAs show-ΓA)))

(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) +ℓ₀))
                                (-@ '+ (list (-x 'x) (-x 'y)) +ℓ₀))
                (-@ '+ (list (-b 1) (-@ '+ (list (-b 2) (-x 'y)) +ℓ₀)) +ℓ₀)))
