#lang racket/base
(require racket/set racket/match racket/list redex/reduction-semantics
         "lib.rkt" "syntax.rkt" "provability.rkt")
(provide (all-defined-out))

(define-judgment-form L
  #:contract (δ σ Γ o [W ...] σ Γ Vns)
  #:mode     (δ I I I I       O O O  )

  ;; Predicates
  [(⊢ Γ W o? ✓)
   ------------------------------------------------------------- "Pred-True"
   (δ σ Γ o? [(name W (_ @ ?e))] σ (Γ+ Γ (o* o? ?e)) 1)]
  [(⊢ Γ W o? X)
   ------------------------------------------------------------- "Pred-False"
   (δ σ Γ o? [(name W (_ @ ?e))] σ (Γ+ Γ (o* not (o* o? ?e))) 0)]
  [(⊢ Γ W o? ?)
   ------------------------------------------------------------- "Pred-Ambig"
   (δ σ Γ o? [W] σ Γ ●)]

  ;; Constructor
  [(where α (?e_1 Γ))        (where β (?e_2 Γ))
   ------------------------------------------------------------- "Cons"
   (δ σ Γ cons [(V_1 @ ?e_1) (V_2 @ ?e_2)] (MM⊔ σ [α ↦ V_1] [β ↦ V_2]) Γ (Cons α β))]

  ;; Accessor
  ; Car
  [(∈ V (lookup σ α))
   ------------------------------------------------------------- "Car-Ok-Conc"
   (δ σ Γ car [((Cons α _) @ _)] σ Γ V)]
  [(side-condition ,(not (●? (term V))))
   (side-condition ,(not (Cons? (term V))))
   ------------------------------------------------------------- "Car-Err-Conc"
   (δ σ Γ car [(name W (V @ _))] σ Γ (blm "car"))]
  [(Γ⊓ Γ (o* cons? ?e) Γ_1)
   ------------------------------------------------------------- "Car-Ok-Abst"
   (δ σ Γ car [(● @ ?e)] σ Γ_1 ●)]
  [(Γ⊓ Γ (o* not (o* cons? ?e)) Γ_1)
   ------------------------------------------------------------- "Car-Err-Abst"
   (δ σ Γ car [(● @ ?e)] σ Γ_1 (blm "car"))]
  
  ; Cdr
  [(∈ V (lookup σ α))
   ------------------------------------------------------------- "Cdr-Ok-Conc"
   (δ σ Γ cdr [((Cons _ α) @ _)] σ Γ V)]
  [(side-condition ,(not (Cons? (term V))))
   (side-condition ,(not (●?    (term V))))
   ------------------------------------------------------------- "Cdr-Err-Conc"
   (δ σ Γ cdr [(name W (V @ _))] σ Γ (blm "cdr"))]
  [(Γ⊓ Γ (o* cons? ?e) Γ_1)
   ------------------------------------------------------------- "Cdr-Ok-Abst"
   (δ σ Γ cdr [(● @ ?e)] σ Γ_1 ●)]
  [(Γ⊓ Γ (o* not (o* cons? ?e)) Γ_1)
   ------------------------------------------------------------- "Cdr-Err-Abst"
   (δ σ Γ cdr [(● @ ?e)] σ Γ_1 (blm "cdr"))]
  

  ;; Arith. HERE
  [------------------------------------------------------------- "Add1-Ok-Conc"
   (δ σ Γ add1 [(_ @ n)] σ Γ ,(+ 1 (term n)))]
  [(side-condition ,(not (integer? (term V))))
   (side-condition ,(not (●?       (term V))))
   ------------------------------------------------------------- "Add1-Err-Conc"
   (δ σ Γ add1 [(V @ n)] σ Γ ,(+ 1 (term n)))]
  [(side-condition ,(not (equal? (term n) (term ?e))))
   ------------------------------------------------------------- "Add1-Widened"
   (δ σ Γ add1 [(n @ ?e)] σ Γ ●)]
  [(Γ⊓ Γ (o* integer? ?e) Γ_1)
   ------------------------------------------------------------- "Add1-Ok-Abs"
   (δ σ Γ add1 [(● @ ?e)] σ Γ_1 ●)]
  [(Γ⊓ Γ (o* not (o* integer? ?e)) Γ_1)
   ------------------------------------------------------------- "Add1-Err-Abs"
   (δ σ Γ add1 [(● @ ?e)] σ Γ_1 ●)]
  )

;; Γ ⊢ W : (✓|X|?)
(define-relation L
  ⊢ ⊆ Γ × W × o? × R
  ;; by Γ
  [(⊢ Γ (● @ ?e) o? ✓+X)
   (Γ⊢ Γ (o* o? ?e) ✓+X)]  
  ;; by V
  [(⊢ _ (V! @ _) o? ✓+X)
   (V⊢ V! o? ✓+X)]
  ;; conservative
  [(⊢ Γ W o? ?)
   (side-condition (not (term (⊢ Γ W o? ✓))))
   (side-condition (not (term (⊢ Γ W o? X))))])

(define-metafunction L
  o* : o ?e ... -> ?e
  [(o* car (cons e _)) e]
  [(o* cdr (cons _ e)) e]
  [(o* cons (car e) (cdr e)) e]
  [(o* not (not e)) e] ; TODO wrong: (not (not 3)) ≠ 1
  [(o* add1 n) ,(+ 1 (term n))]
  [(o* o e ...) (o e ...)]
  [(o* o _ ...) #f])

;; restrict environemnts `ρ` and `Γ` to `FV⟦E⟧`
(define-metafunction L
  restrict : e ρ Γ -> (ρ Γ)
  [(restrict e ρ Γ)
   ,(let ([xs (term (FV e))])
      (term (,(for/hash ([(k v) (in-hash (term ρ))] #:when (set-member? xs k))
                 (values k v))
             ,(for/set ([e (in-set (term Γ))] #:when (subset? (term (FV ,e)) xs))
                e))))])


;; Force enviornment to split to #t/#f
(define-judgment-form L
  #:contract (split Γ W boolean Γ)
  #:mode     (split I I O       O)
  [(side-condition ,(not (equal? (term V) 0)))
   (side-condition ,(not (●? (term V))))
   ----------------------------------------- "Split-True-V"
   (split Γ (V @ ?e) #t (Γ+ Γ ?e))]
  [(where #f (Γ⊢ Γ ?e X))
   ----------------------------------------- "Split-True-Γ"
   (split Γ (● @ ?e) #t (Γ+ Γ ?e))]
  [----------------------------------------- "Split-False-V"
   (split Γ (0 @ ?e) #f (Γ+ Γ (o* not ?e)))]
  [(where #f (Γ⊢ Γ ?e ✓))
   ----------------------------------------- "Split-False-Γ"
   (split Γ (● @ ?e) #f (Γ+ Γ (o* not ?e)))])

(module+ test
  (require rackunit)
  )
