#lang typed/racket/base

(provide (all-defined-out))

(require racket/match racket/set "../utils/main.rkt" "definition.rkt")

(: σ@/list : -σ (Listof -α) → (℘ (Listof -V)))
;; Look up store at addresses. Return all possible combinations
(define (σ@/list σ αs)
  (match αs
    [(cons α αs*)
     (define-values (Vs _) (σ@ σ α))
     (define Vss (σ@/list σ αs*))
     (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
       (cons V Vs))]
    ['() {set '()}]))

(: σ@¹ : -σ -α → -V)
;; Look up store, asserting that exactly 1 value resides there
(define (σ@¹ σ α)
  (define-values (Vs _) (σ@ σ α))
  (assert (= 1 (set-count Vs)))
  (set-first Vs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Restrict stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: σr->αs : -σr → (℘ -α))
(define (σr->αs σr)
  (match-define (-σr Vs _) σr)
  (for/union : (℘ -α) ([V Vs]) (V->αs V)))

(: V->αs : -V → (℘ -α))
(define V->αs
  (match-lambda
    [(-St _ αs) (list->set αs)]
    [(-Vector αs) (list->set αs)]
    [(-Ar V α _) (set-add (V->αs V) α)]
    [(-St* _ γs α _) (set-add (for/set: : (℘ -α) ([γ γs] #:when γ) γ) α)]
    [(-Vector/hetero γs _) (list->set γs)]
    [(-Vector/homo α _) {set α}]
    [(-Clo _ _ ρ _) (ρ->αs ρ)]
    [(-Case-Clo _ ρ _) (ρ->αs ρ)]
    [(-And/C _ α β) {set α β}]
    [(-Or/C  _ α β) {set α β}]
    [(-Not/C α) {set α}]
    [(-x/C α) {set α}]
    [(-St/C _ _ αs) {list->set αs}]
    [(-Vectorof α) {set α}]
    [(-Vector/C αs) (list->set αs)]
    [(-=> αs α _) (set-add (list->set αs) α)]
    [(-=>i αs _ _) (list->set αs)]
    [(-Case-> clauses _)
     (for/union : (℘ -α) ([clause clauses])
                (match-define (cons αs α) clause)
                (set-add (list->set αs) α))]
    [_ ∅]))

(: ρ->αs : -ρ → (℘ -α))
(define (ρ->αs ρ)
  (for/set: : (℘ -α) ([α (in-hash-values ρ)]) α))

(: span-σ : (HashTable -α -σr) (℘ -α) → (HashTable -α -σr))
(define (span-σ σ αs) (m↓ σ (span σ αs σr->αs)))

(: Γ->αs : -Γ → (℘ -αₖ))
(define (Γ->αs Γ)
  (match-define (-Γ _ _ γs) Γ)
  (for/set: : (℘ -αₖ) ([γ γs])
    (-γ-callee γ)))

(: ΓA->αs : -ΓA → (℘ -αₖ))
(define (ΓA->αs ΓA)
  (match-define (-ΓA Γ _) ΓA)
  (Γ->αs Γ))

(: span-M : (HashTable -αₖ (℘ -ΓA)) (℘ -αₖ) → (HashTable -αₖ (℘ -ΓA)))
(define (span-M M αs) (m↓ M (span* M αs ΓA->αs)))

(: κ->αs : -κ -> (℘ -αₖ))
(define (κ->αs κ)
  (match-define (-κ _ _ _ _) κ)
  (error 'κ->αs "TODO"))

(: span-σₖ : (HashTable -αₖ (℘ -κ)) (℘ -αₖ) → (HashTable -αₖ (℘ -κ)))
(define (span-σₖ σₖ αs) (m↓ σₖ (span* σₖ αs κ->αs)))
