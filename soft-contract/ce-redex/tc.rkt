#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics "lib.rkt" "lang.rkt")

(define-judgment-form SCPCF
  #:contract (⊢ₜ Γ E T)
  #:mode     (⊢ₜ I I O)
  [(⊢ₜ _ (↓ T _) T)]
  [(⊢ₜ _ n ℤ)]
  [(⊢ₜ (++ Γ [X ↦ T]) E T_1)
   -----------------------------------------------
   (⊢ₜ Γ (λ (X : T) E) (T → T_1))]
  [(⊢ₜ _ (• T _) T)]
  [(⊢ₜ Γ X (@ Γ X))]
  [(⊢ₜ Γ E ℤ)    (⊢ₜ Γ E_t T)    (⊢ₜ Γ E_f T)
   -----------------------------------------------
   (⊢ₜ Γ (if E E_t E_f) T)]
  [(⊢ₜ Γ E_f (T_x → T))    (⊢ₜ Γ E_x T_x)
   -----------------------------------------------
   (⊢ₜ Γ (E_f E_x) T)]
  [(⊢ₜ Γ E T) ...     (Δ O [T ...] T_a)
   -----------------------------------------------
   (⊢ₜ Γ (O E ... L) T_a)])

(define-judgment-form SCPCF
  #:contract (Δ O [T ...] T)
  #:mode     (Δ I O       O)
  [(Δ O¹ (ℤ) ℤ)]
  [(Δ O² (ℤ ℤ) ℤ)])

(define-metafunction SCPCF
  tc : E -> T or #f
  [(tc E) T (judgment-holds (⊢ₜ {} E T))]
  [(tc _) #f])

(define-metafunction SCPCF
  tc-S : S -> T
  [(tc-S n) ℤ]
  [(tc-S (• T _ ...)) T]
  [(tc-S (name V (λ (X : T) E))) (tc V)]
  [(tc-S (case T _ ...)) (ℤ → T)])

(module+ test
  (require rackunit)
  (define-syntax-rule (==> E T)
    (test-case (format "~a : ~a~n" (term E) (term T))
               (check-equal? (judgment-holds (⊢ₜ {} E T_a) T_a) (term (T)))))
  (8 . ==> . ℤ)
  ((λ (x : ℤ) x) . ==> . (ℤ → ℤ))
  ((λ (g : (ℤ → ℤ)) (λ (n : ℤ) (/ 1 (- 100 (g n) Λ) Λ)))
   . ==> . ((ℤ → ℤ) → (ℤ → ℤ)))
  ((λ (f : ((ℤ → ℤ) → (ℤ → ℤ)))
     ((f (λ (n : ℤ) (if (= n 0 Λ) 100 0))) 0))
   . ==> . (((ℤ → ℤ) → (ℤ → ℤ)) → ℤ))
  ((LET* ([f : ((ℤ  → ℤ) → (ℤ → ℤ))
             (λ (g : (ℤ → ℤ))
               (λ (n : ℤ)
                 (/ 1 (- 100 (g n) L-) L/)))])
         ((λ (f : ((ℤ  → ℤ) → (ℤ → ℤ)))
            ((f (λ (n : ℤ)
                  (if (= n 0 L=) 100 0)))
             0))
          f))
   . ==> . ℤ)
  ((LET* ([f : ((ℤ  → ℤ) → (ℤ → ℤ))
             (λ (g : (ℤ → ℤ))
               (λ (n : ℤ)
                 (/ 1 (- 100 (g n) L-) L/)))])
         ((• (((ℤ  → ℤ) → (ℤ → ℤ)) → ℤ) L•) f))
   . ==> . ℤ))
