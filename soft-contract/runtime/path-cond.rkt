#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "definition.rkt"
         "simp.rkt")

(: s↓ : -s (℘ Symbol) → -s)
;; Restrict symbol to given set of free variables
(define (s↓ s xs)
  (and s (e↓ s xs)))
(: e↓ : -e (℘ Symbol) → -s)
(define (e↓ e xs)
  (and (not (set-empty? (∩ (fv e) xs))) #;(⊆ (fv e) xs) e))

(: es↓ : (℘ -e) (℘ Symbol) → (℘ -e))
(define (es↓ es xs)
  (for*/set: : (℘ -e) ([e es]
                       [e* (in-value (e↓ e xs))] #:when e*)
     e*))

(: Γ↓ : -Γ (℘ Symbol) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)
  (match-define (-Γ φs as γs) Γ)
  (define φs* (es↓ φs xs))
  (define as*
    (for/hasheq : (HashTable Symbol -e) ([(x e) as] #:when (∋ xs x))
      (values x e)))
  (define γs*
    (for*/list : (Listof -γ) ([γ (in-list γs)]
                              [sₓs (in-value (-γ-args γ))]
                              [sₕ (in-value (-γ-fun γ))]
                              [s (in-value (and sₕ (andmap -e? sₓs) (-@ sₕ sₓs +ℓ₀)))]
                              [s* (in-value (s↓ s xs))] #:when s*)
      γ))
  (-Γ φs* as* γs*))

(: canonicalize : (U -Γ (HashTable Symbol -e)) Symbol → -e)
;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize X x)
  (cond [(-Γ? X) (canonicalize (-Γ-aliases X) x)]
        [else (hash-ref X x (λ () (-x x)))]))

;; Return an expression canonicalizing given expression in terms of lexically farthest possible variable(s)
(: canonicalize-e : (U -Γ (HashTable Symbol -e)) -e → -e)
(define (canonicalize-e X e)
  (cond [(-Γ? X) (canonicalize-e (-Γ-aliases X) e)]
        [else (e/map (for/hash : Subst ([(x eₓ) X]) (values (-x x) eₓ)) e)]))

(: -Γ-plus-γ : -Γ -γ → -Γ)
(define (-Γ-plus-γ Γ γ)
  (match-define (-γ αₖ ?blm sₕ sₓs) γ)
  (match-define (-Γ φs as γs) Γ)
  (cond [(and (not (-ℋ𝒱? αₖ))
              (or sₕ (ormap (inst values -s) sₓs))
              (not (member γ γs)))
         (-Γ φs as (cons γ γs))]
        [else Γ]))

(: γ->fargs : -γ → -s)
(define (γ->fargs γ)
  (match-define (-γ _ _ sₕ sₓs) γ)
  (apply -?@ sₕ sₓs))

(: fvₛ : -s → (℘ Symbol))
(define (fvₛ s) (if s (fv s) ∅eq))

(: invalidate : -Γ Symbol → -Γ)
;; Throw away anything known about `x` in `Γ`
(define (invalidate Γ x)
  (with-debugging/off
    ((Γ*)
     (match-define (-Γ φs as γs) Γ)
     (define φs*
       (for/set: : (℘ -e) ([φ φs] #:unless (∋ (fv φ) x))
         φ))
     (define as*
       (for/hasheq : (HashTable Symbol -e) ([(z φ) as]
                                              #:unless (eq? z x)
                                              #:unless (∋ (fv φ) x))
         (values z φ)))
     (define γs*
       (for*/list : (Listof -γ) ([γ (in-list γs)]
                                 [αₖ (in-value (-γ-callee γ))]
                                 [blm (in-value (-γ-blm γ))]
                                 [sₓs (in-value (-γ-args γ))]
                                 [sₕ (in-value (-γ-fun γ))]
                                 [sₓs* (in-value (for/list : (Listof -s) ([sₓ sₓs])
                                                   (and (not (∋ (fvₛ sₓ) x)) sₓ)))]
                                 #:when (ormap (inst values -s) sₓs*)
                                 [sₕ* (in-value (and (not (∋ (fvₛ sₕ) x)) sₕ))])
         (-γ αₖ blm sₕ* sₓs*)))
     (-Γ φs* as* γs*))
    (printf "invalidate ~a:~n- before: ~a~n- after: ~a~n~n" x (show-Γ Γ) (show-Γ Γ*))))

(: predicates-of : (U -Γ (℘ -e)) -s → (℘ -v))
;; Extract type-like contracts on given symbol
(define (predicates-of Γ s)
  (cond
    [(-Γ? Γ) (predicates-of (-Γ-facts Γ) s)]
    [else
     ;; tmp hack for integer precision
     (define ps : (℘ -v)
       (match s
         [(-@ '- (list e₁ e₂) _)
          (cond [(or (∋ Γ (-@ '<= (list e₂ e₁) +ℓ₀))
                     (∋ Γ (-@ '>= (list e₁ e₂) +ℓ₀)))
                 {set (-≥/c 0)}]
                [(or (∋ Γ (-@ '< (list e₂ e₁) +ℓ₀))
                     (∋ Γ (-@ '> (list e₁ e₂) +ℓ₀)))
                 {set (->/c 0)}]
                [else ∅])]
         [_ ∅]))
     (for/fold ([ps : (℘ -v) ps]) ([φ (in-set Γ)])
       (match φ
         ;; unary
         [(-@ 'negative? (list (== s)) _) (set-add ps (-</c 0))]
         [(-@ 'positive? (list (== s)) _) (set-add ps (->/c 0))]
         [(-@ (? -o? o)  (list (== s)) _) (set-add ps o)]
         ;; binary
         [(-@ (? -o? o) (list (== s) (and v (? -v?) (? closed?))) _)
          (set-add ps (-λ '(𝒙) (-@ o (list (-x '𝒙) v) +ℓ₀)))]
         [(-@ (? -o? o) (list (and v (? -v?) (? closed?)) (== s)) _)
          (set-add ps (-λ '(𝒙) (-@ o (list v (-x '𝒙)) +ℓ₀)))]
         ;; negate unary
         [(-@ 'not (list (-@ (? -o? o) (list (== s)) _)) _)
          (set-add ps (-not/c o))]
         ;; negate binary
         [(-@ 'not (list (-@ (? -o? o) (list (== s) (and v (? -v?) (? closed?))) _)) _)
          (set-add ps (-λ '(𝒙) (-@/simp 'not (-@/simp o (-x '𝒙) v))))]
         [(-@ 'not (list (-@ (? -o? o) (list (and v (? -v?) (? closed?)) (== s)) _)) _)
          (set-add ps (-λ '(𝒙) (-@/simp 'not (-@/simp o v (-x '𝒙)))))]
         [_ ps]))]))
