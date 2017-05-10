#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "definition.rkt")

(: σ@ : (U -Σ -σ) ⟪α⟫ → (℘ -V))
(define (σ@ m ⟪α⟫)
  (define σ (if (-Σ? m) (-Σ-σ m) m))
  (with-debugging/off
    ((Vs)
     (hash-ref (-σ-m σ) ⟪α⟫ (λ () (error 'σ@ "no address ~a" (⟪α⟫->-α ⟪α⟫)))))
    (when (>= (set-count Vs) 5)
      (printf "σ@: ~a -> ~a~n" (show-⟪α⟫ ⟪α⟫) (set-count Vs))
      (define-set roots : ⟪α⟫ #:eq? #t)
      (for ([V Vs])
        (roots-union! (V->⟪α⟫s V))
        (printf "  - ~a~n" (show-V V)))
      (printf "addresses:~n")
      (for ([(α Vs) (span-σ (-σ-m σ) roots)])
        (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α ⟪α⟫)) (set-map Vs show-V)))
      (printf "~n")
      (when (> ⟪α⟫ 3000)
        (error "DONE")))))

(: defined-at? : (U -Σ -σ) ⟪α⟫ → Boolean)
(define (defined-at? σ α)
  (cond [(-Σ? σ) (defined-at? (-Σ-σ σ) α)]
        [else (and (hash-has-key? (-σ-m σ) α)
                   (not (∋ (hash-ref (-σ-m σ) α) 'undefined)))]))

(: mutated? : (U -Σ -σ) ⟪α⟫ → Boolean)
(define (mutated? m ⟪α⟫)
  (∋ (-σ-modified (if (-Σ? m) (-Σ-σ m) m)) ⟪α⟫))

(: σ-remove : -σ ⟪α⟫ -V → -σ)
(define (σ-remove σ ⟪α⟫ V)
  (match-define (-σ m crds mods) σ)
  (define m* (hash-update m ⟪α⟫ (λ ([Vs : (℘ -V)]) (set-remove Vs V))))
  (-σ m* crds mods))

(: σ-remove! : -Σ ⟪α⟫ -V → Void)
(define (σ-remove! Σ ⟪α⟫ V)
  (define σ (-Σ-σ Σ))
  (set--Σ-σ! Σ (σ-remove σ ⟪α⟫ V)))

(: σ@/list : (U -Σ -σ) (Listof ⟪α⟫) → (℘ (Listof -V)))
;; Look up store at addresses. Return all possible combinations
(define (σ@/list m ⟪α⟫s)
  (define σ (if (-Σ? m) (-Σ-σ m) m))
  (with-debugging/off
    ((ans)
     (let loop : (℘ (Listof -V)) ([⟪α⟫s : (Listof ⟪α⟫) ⟪α⟫s])
          (match ⟪α⟫s
            [(cons ⟪α⟫ ⟪α⟫s*)
             (define Vs (σ@ σ ⟪α⟫))
             (define Vss (loop ⟪α⟫s*))
             (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
               (cons V Vs))]
            ['() {set '()}])))
    (when (> (set-count ans) 1)
      (printf "σ@/list: ~a -> ~a~n" (map show-⟪α⟫ ⟪α⟫s) (set-count ans)))))

(: σ@¹ : (U -Σ -σ) ⟪α⟫ → -V)
;; Look up store, asserting that exactly 1 value resides there
(define (σ@¹ m ⟪α⟫)
  (define Vs (σ@ m ⟪α⟫))
  (assert (= 1 (set-count Vs)))
  (set-first Vs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Restrict stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memoeq (V->⟪α⟫s [V : -V]) : (℘ ⟪α⟫)
  (with-debugging/off
    ((αs)
     (match V
       [(-St _ αs) (list->seteq αs)]
       [(-Vector αs) (list->seteq αs)]
       [(-Vector^ α _) {seteq α}]
       [(-Ar V α _) (set-add (V->⟪α⟫s V) α)]
       [(-St* grd α _) (set-add (V->⟪α⟫s grd) α)]
       [(-Vector/guard grd ⟪α⟫ _) (set-add (V->⟪α⟫s grd) ⟪α⟫)]
       [(-Clo _ _ ρ _) (ρ->⟪α⟫s ρ)]
       [(-Case-Clo _ ρ _) (ρ->⟪α⟫s ρ)]
       [(-And/C _ α β) {seteq (-⟪α⟫ℓ-addr α) (-⟪α⟫ℓ-addr β)}]
       [(-Or/C  _ α β) {seteq (-⟪α⟫ℓ-addr α) (-⟪α⟫ℓ-addr β)}]
       [(-Not/C α) {seteq (-⟪α⟫ℓ-addr α)}]
       [(-One-Of/C _) ∅eq]
       [(-x/C α) {seteq α}]
       [(-St/C _ _ αs) {list->seteq (map -⟪α⟫ℓ-addr αs)}]
       [(-Vectorof α) {seteq (-⟪α⟫ℓ-addr α)}]
       [(-Vector/C αs) (list->seteq (map -⟪α⟫ℓ-addr αs))]
       [(-=> αs βs _)
        (match αs
          [(? list? αs) (set-add* (list->seteq (map -⟪α⟫ℓ-addr αs)) (map -⟪α⟫ℓ-addr βs))]
          [(-var αs αᵣ)
           (set-add* (set-add (list->seteq (map -⟪α⟫ℓ-addr αs)) (-⟪α⟫ℓ-addr αᵣ))
                     (map -⟪α⟫ℓ-addr βs))])]
       [(-=>i αs (list D _ _) _) (∪ (list->seteq (map -⟪α⟫ℓ-addr αs)) (V->⟪α⟫s D))]
       [(-Case-> clauses _)
        (for/unioneq : (℘ ⟪α⟫) ([clause clauses])
          (match-define (cons αs α) clause)
          (set-add (list->seteq αs) α))]
       [_ ∅eq]))
    (printf "V->⟪α⟫s ~a: (~a)~n" (show-V V) (set-count αs))
    (for ([α αs])
      (printf " - ~a~n" α))
    (printf "~n")))

(: ρ->⟪α⟫s : -ρ → (℘ ⟪α⟫))
(define (ρ->⟪α⟫s ρ)
  (for/seteq: : (℘ ⟪α⟫) ([⟪α⟫ : ⟪α⟫ (in-hash-values ρ)]) ⟪α⟫))

(: span-σ : (HashTable ⟪α⟫ (℘ -V)) (℘ ⟪α⟫) → (HashTable ⟪α⟫ (℘ -V)))
(define (span-σ σ αs)
  (hash-copy/spanning* σ αs V->⟪α⟫s))

(: t->αₖs : -?t → (℘ -αₖ))
(define (t->αₖs t)
  (match t
    [(-t.@ h ts)
     (for/fold ([acc : (℘ -αₖ) (if (-αₖ? h) {set h} ∅)])
               ([t (in-list ts)])
       (∪ acc (t->αₖs t)))]
    [_ ∅]))

(: Γ->αₖs : -Γ → (℘ -αₖ))
(define (Γ->αₖs Γ)
  (for/union : (℘ -αₖ) ([t (-Γ-facts Γ)])
    (t->αₖs t)))

(: ΓA->αₖs : -ΓA → (℘ -αₖ))
(define (ΓA->αₖs ΓA)
  (match-define (-ΓA Γ A) ΓA)
  (define s₀
    (match A
      [(-W _ t) (t->αₖs t)]
      [_ ∅]))
  (for/fold ([acc : (℘ -αₖ) s₀]) ([φ (in-set Γ)])
    (∪ acc (t->αₖs φ))))

(: αₖ->⟪α⟫s : -αₖ (HashTable -αₖ (℘ -κ)) → (℘ ⟪α⟫))
(define (αₖ->⟪α⟫s αₖ σₖ)
  (define-set seen : -αₖ #:as-mutable-hash? #t)
  (let go ([acc : (℘ ⟪α⟫) ∅eq] [αₖ : -αₖ αₖ])
    (cond
      [(seen-has? αₖ) acc]
      [else
       (seen-add! αₖ)
       (for/fold ([acc : (℘ ⟪α⟫) (if (-ℋ𝒱? αₖ) (set-add acc ⟪α⟫ₕᵥ) acc)])
                 ([κ (in-set (hash-ref σₖ αₖ mk-∅))])
         (define ⟦k⟧ (-κ-cont κ))
         (go (∪ acc (⟦k⟧->roots ⟦k⟧)) (⟦k⟧->αₖ ⟦k⟧)))])))

(: span-M : (HashTable -αₖ (℘ -ΓA)) (℘ -αₖ) → (HashTable -αₖ (℘ -ΓA)))
(define (span-M M αs)
  (hash-copy/spanning* M αs ΓA->αₖs))

#;(: soft-gc! : -σ (℘ ⟪α⟫) → Void)
;; "garbage collect" mutated-ness cardinality information 
#;(define (soft-gc! σ αs)
  (match-define (-σ _ mods crds) σ)
  (for ([α (in-set mods)] #:unless (∋ αs α))
    (hash-remove! mods α))
  (for ([α (in-list (hash-keys crds))] #:unless (∋ αs α))
    (hash-remove! crds α)))

(define (->⟪α⟫s [x : (Rec X (U ⟪α⟫ -V -W¹ -W -ρ (-var X) (Listof X) (℘ X)))]) : (℘ ⟪α⟫)
  (cond
    [(-var? x)
     (∪ (->⟪α⟫s (-var-rest x))
        (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-list (-var-init x))]) (->⟪α⟫s xᵢ)))]
    [(list? x)
     (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-list x)]) (->⟪α⟫s xᵢ))]
    [(set? x)
     (for/unioneq : (℘ ⟪α⟫) ([xᵢ (in-set x)]) (->⟪α⟫s xᵢ))]
    [(-V? x) (V->⟪α⟫s x)]
    [(-W¹? x) (V->⟪α⟫s (-W¹-V x))]
    [(-W? x) (->⟪α⟫s (-W-Vs x))]
    [(hash? x) (ρ->⟪α⟫s x)]
    [else {seteq x}]))

(: σ-equal?/spanning-root : -σ -σ (℘ ⟪α⟫) → Boolean)
(define (σ-equal?/spanning-root σ₁ σ₂ root)
  (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-σ store₁ mutated₁ cardinalities₁) σ₁)
  (match-define (-σ store₂ mutated₂ cardinalities₂) σ₂)
  
  (let go ([addrs : (℘ ⟪α⟫) root])
    (for/and : Boolean ([α : ⟪α⟫ (in-set addrs)])
      (cond
        [(seen-has? α) #t]
        [else
         (seen-add! α)
         (and (equal? (∋ mutated₁ α) (∋ mutated₂ α))
              (equal? (hash-ref cardinalities₁ α (λ () 0))
                      (hash-ref cardinalities₂ α (λ () 0)))
              (let ([Vs₁ (hash-ref store₁ α mk-∅)]
                    [Vs₂ (hash-ref store₂ α mk-∅)])
                (and (equal? Vs₁ Vs₂)
                     (for/and : Boolean ([V (in-set Vs₁)])
                       (go (V->⟪α⟫s V))))))]))))
