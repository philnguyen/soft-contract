#lang racket/base

(provide (all-defined-out))
(require redex/reduction-semantics "syntax.rkt" "proof-relation.rkt")

;; Might look tedious, but these would be generated in a real implementation

(define-metafunction λ-sym
  δ : l M Γ o W -> (Γ A)
  [(δ _ M Γ o? (name W (_ @ S)))
   (Γ (●-integer @ (@S o? S)))
   (where ? (MΓ⊢oW M Γ o? W))]
  [(δ _ M Γ o? (name W (_ @ S)))
   (Γ (1 @ (@S o? S)))
   (where ✓ (MΓ⊢oW M Γ o? W))]
  [(δ _ M Γ o? (name W (_ @ S)))
   (Γ (0 @ (@S o? S)))
   (where ✗ (MΓ⊢oW M Γ o? W))]
  [(δ _ M Γ add1 (_ @ n))
   (Γ (n_1 @ n_1))
   (where n_1 ,(+ 1 (term n)))]
  [(δ _ M Γ add1 (name W (_ @ S)))
   (Γ_ok (●-integer @ (@S add1 S)))
   (where (Γ_ok _) (MΓ+/-oW M Γ integer? W))]
  [(δ l M Γ add1 W)
   (Γ_bad (blame l "add1 non-integer"))
   (where (_ Γ_bad) (MΓ+/-oW M Γ integer? W))])

