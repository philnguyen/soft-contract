#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "definition.rkt")

(: σ@ : -σ -α → (℘ -V))
(define (σ@ σ α)
  (with-debugging/off
    ((Vs old?)
     (hash-ref (-σ-m σ) α (λ () (error 'σ@ "no address ~a" α))))
    (when (>= (set-count Vs) 2)
      (printf "σ@: ~a -> ~a~n" α (set-count Vs))
      (define-set roots : -α)
      (for ([V Vs])
        (roots-union! (V->αs V))
        (printf "  - ~a~n" (show-V V)))
      (printf "addresses:~n")
      (for ([row (show-σ (span-σ (-σ-m σ) roots))])
        (printf "  - ~a~n" row))
      (printf "~n")
      #;(error "done"))))

(: σ-old? : -σ -α → Boolean)
(define (σ-old? σ α)
  (not (∋ (-σ-modified σ) α)))

(: σ-remove! : -σ -α -V → Void)
(define (σ-remove! σ α V)
  (define m* (hash-update (-σ-m σ) α (λ ([Vs : (℘ -V)]) (set-remove Vs V))))
  (set--σ-m! σ m*))

(: σ@/list : -σ (Listof -α) → (℘ (Listof -V)))
;; Look up store at addresses. Return all possible combinations
(define (σ@/list σ αs)
  (with-debugging/off
    ((ans)
     (let loop : (℘ (Listof -V)) ([αs : (Listof -α) αs])
          (match αs
            [(cons α αs*)
             (define Vs (σ@ σ α))
             (define Vss (loop αs*))
             (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
               (cons V Vs))]
            ['() {set '()}])))
    (when (> (set-count ans) 1)
      (printf "σ@/list: ~a -> ~a~n" (map show-α αs) (set-count ans)))))

(: σ@¹ : -σ -α → -V)
;; Look up store, asserting that exactly 1 value resides there
(define (σ@¹ σ α)
  (define Vs (σ@ σ α))
  (assert (= 1 (set-count Vs)))
  (set-first Vs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Restrict stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: V->αs : -V → (℘ -α))
(define (V->αs V)
  (with-debugging/off
    ((αs)
     (match V
       [(-St _ αs) (list->set αs)]
       [(-Vector αs) (list->set αs)]
       [(-Ar V α _) (set-add (V->αs V) α)]
       [(-St* _ γs α _) (set-add (for/set: : (℘ -α) ([γ γs] #:when γ) γ) α)]
       [(-Vector/hetero γs _) (list->set γs)]
       [(-Vector/homo α _) {set α}]
       [(-Clo _ _ ρ _) (ρ->αs ρ)]
       [(-Case-Clo _ ρ _) (ρ->αs ρ)]
       [(-And/C _ α β) {set (αℓ->α α) (αℓ->α β)}]
       [(-Or/C  _ α β) {set (αℓ->α α) (αℓ->α β)}]
       [(-Not/C α) {set (αℓ->α α)}]
       [(-x/C α) {set α}]
       [(-St/C _ _ αs) {list->set (map αℓ->α αs)}]
       [(-Vectorof α) {set (αℓ->α α)}]
       [(-Vector/C αs) (list->set (map αℓ->α αs))]
       [(-=> αs α _) (set-add (list->set (map αℓ->α αs)) (αℓ->α α))]
       [(-=>i αs _ _) (list->set (map αℓ->α αs))]
       [(-Case-> clauses _)
        (for/union : (℘ -α) ([clause clauses])
                   (match-define (cons αs α) clause)
                   (set-add (list->set αs) α))]
       [_ ∅]))
    (printf "V->αs ~a: (~a)~n" (show-V V) (set-count αs))
    (for ([α αs])
      (printf " - ~a~n" α))
    (printf "~n")))

(: ρ->αs : -ρ → (℘ -α))
(define (ρ->αs ρ)
  (for/set: : (℘ -α) ([α (in-hash-values ρ)]) α))

(: span-σ : (HashTable -α (℘ -V)) (℘ -α) → (HashTable -α (℘ -V)))
(define (span-σ σ αs) (m↓ σ (span* σ αs V->αs)))

(: Γ->αₖs : -Γ → (℘ -αₖ))
(define (Γ->αₖs Γ)
  (match-define (-Γ _ _ γs) Γ)
  (for/set: : (℘ -αₖ) ([γ γs])
    (-γ-callee γ)))

(: ΓA->αₖs : -ΓA → (℘ -αₖ))
(define (ΓA->αₖs ΓA)
  (match-define (-ΓA Γ _) ΓA)
  (Γ->αₖs Γ))

(: αₖ->αs : -αₖ (HashTable -αₖ (℘ -κ)) → (℘ -α))
(define (αₖ->αs αₖ σₖ)
  (define-set seen : -αₖ)
  (define-set αs   : -α)
  (let touch! ([αₖ : -αₖ αₖ])
    (unless (seen-has? αₖ)
      (seen-add! αₖ)
      (for ([κ (in-set (hash-ref σₖ αₖ →∅))])
        (define ⟦k⟧ (-κ-cont κ))
        (αs-union! (⟦k⟧->roots ⟦k⟧))
        (touch! (⟦k⟧->αₖ ⟦k⟧)))))
  αs)

(: span-M : (HashTable -αₖ (℘ -ΓA)) (℘ -αₖ) → (HashTable -αₖ (℘ -ΓA)))
(define (span-M M αs) (m↓ M (span* M αs ΓA->αₖs)))

(: span-σₖ : (HashTable -αₖ (℘ -κ)) -αₖ → (℘ -αₖ))
;; Compute stack addresses in `σₖ` reachable from `αₖ`
(define (span-σₖ σₖ αₖ)
  (with-debugging/off
    ((αₖs)
     (span* σₖ
            {set αₖ}
            (λ ([κ : -κ])
              {set (⟦k⟧->αₖ (-κ-cont κ))})))
    (printf "span-σₖ:~n")
    (printf " - σₖ: (~a) ~n" (hash-count σₖ))
    (for ([(k v) (in-hash σₖ)])
      (printf "   + ~a ↦ (~a)~n" (show-αₖ k) (set-count v))
      (for ([vᵢ v])
        (printf "     * ~a~n" (show-κ vᵢ))))
    (printf " - αₖ: ~a~n" (show-αₖ αₖ))
    (printf " - res: (~a) ~n" (set-count αₖs))
    (for ([αₖ αₖs])
      (printf "   + ~a~n" (show-αₖ αₖ)))
    (printf "~n")))

(: soft-gc! : -σ (℘ -α) → Void)
;; "garbage collect" mutated-ness cardinality information 
(define (soft-gc! σ αs)
  (match-define (-σ _ mods crds) σ)
  (set--σ-modified! σ (∩ mods αs))
  (set--σ-cardinality! σ (m↓ crds αs)))

(define/memoeq (->αs [x : (Rec X (U -α -V -W¹ -W -ρ (Listof X)))]) : (℘ -α)
  (cond
    [(list? x)
     (for/union : (℘ -α) ([xᵢ x]) (->αs xᵢ))]
    [(-V? x) (V->αs x)]
    [(-W¹? x) (V->αs (-W¹-V x))]
    [(-W? x) (->αs (-W-Vs x))]
    [(hash? x) (ρ->αs x)]
    [else {set x}]))
