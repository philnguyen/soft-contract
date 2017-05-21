#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "signatures.rkt")

(define-unit sto@
  (import)
  (export sto^)

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

  (define ⟪α⟫ₕᵥ (-α->⟪α⟫ (-α.hv)))
  (define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.fn.●)))
  (define ⊥σ (-σ (hasheq ⟪α⟫ₕᵥ ∅) ∅eq (hasheq)))

  (: cardinality+ : -cardinality → -cardinality)
  (define (cardinality+ c)
    (case c
      [(0) 1]
      [(1) 'N]
      [else 'N]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Kontinuation store
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ⊥σₖ : -σₖ (hash))

  (: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -κ))
  (define (σₖ@ m αₖ)
    (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ mk-∅))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Memo table
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ⊥M : -M (hash))

  (: M@ : (U -Σ -M) -αₖ → (℘ -ΓA))
  (define (M@ m αₖ) (hash-ref (if (-Σ? m) (-Σ-M m) m) αₖ mk-∅))

  (define (⊥Σ) (-Σ ⊥σ ⊥σₖ ⊥M))
  )


