#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics racket/set racket/match
         "lib.rkt" "lang.rkt" "tc.rkt" "proof-system-ext.rkt")

(define-judgment-form SCPCF
  #:contract (δ L Σ O [L ...] δ↓ Σ)
  #:mode     (δ I I I I       O  O)
  ;; 1-arg pred
  [(where #t (proves Σ L Zero?))
   -----------------------------------------------
   (δ _ Σ zero? [L] 1 Σ)]
  [(where #t (refutes Σ L Zero?))
   -----------------------------------------------
   (δ _ Σ zero? [L] 0 Σ)]
  [(where #t (neither Σ L Zero?))
   -----------------------------------------------
   (δ _ Σ zero? [L] 1 (Σ⊓ Σ L Zero?))]
  [(where #t (neither Σ L Zero?))
   -----------------------------------------------
   (δ _ Σ zero? [L] 0 (Σ⊓ Σ L (¬/P Zero?)))]
  ;; 2-arg preds
  [(where #t (proves Σ L_1 (λ (x : ℤ) (< x (↓ ℤ L_2) Λ))))
   -----------------------------------------------
   (δ _ Σ < [L_1 L_2] 1 Σ)]
  [(where #t (refutes Σ L_1 (λ (x : ℤ) (< x (↓ ℤ L_2) Λ))))
   -----------------------------------------------
   (δ _ Σ < [L_1 L_2] 0 Σ)]
  [(where P (λ (x : ℤ) (< x (↓ ℤ L_2) Λ)))
   (where #t (neither Σ L_1 P))
   -----------------------------------------------
   (δ _ Σ < [L_1 L_2] 1 (Σ⊓ Σ L_1 P))]
  [(where P (λ (x : ℤ) (< x (↓ ℤ L_2) Λ)))
   (where #t (neither Σ L_1 P))
   -----------------------------------------------
   (δ _ Σ < [L_1 L_2] 0 (Σ⊓ Σ L_1 (¬/P P)))]
  ;; >, ≥, ≤ in terms of <
  [(δ L Σ < [L_2 L_1] n Σ_1)
   -----------------------------------------------
   (δ L Σ > [L_1 L_2] n Σ_1)]
  [(δ L Σ < [L_1 L_2] n Σ_1)
   -----------------------------------------------
   (δ L Σ ≥ [L_1 L_2] ,(- 1 (term n)) Σ_1)]
  [(δ L Σ ≥ [L_2 L_1] n Σ_1)
   -----------------------------------------------
   (δ L Σ ≤ [L_1 L_2] n Σ_1)]
  [(proves Σ L_1 (λ (x : ℤ) (= x (↓ ℤ L_2) Λ)))
   -----------------------------------------------
   (δ _ Σ = [L_1 L_2] 1 Σ)]
  [(refutes Σ L_1 (λ (x : ℤ) (= x (↓ ℤ L_2) Λ)))
   -----------------------------------------------
   (δ _ Σ = [L_1 L_2] 0 Σ)]
  [(where P (λ (x : ℤ) (= x (↓ ℤ L_2) Λ)))
   (neither Σ L_1 P)
   -----------------------------------------------
   (δ _ Σ = [L_1 L_2] 1 (Σ⊓ Σ L_1 P))]
  [(where P (λ (x : ℤ) (= x (↓ ℤ L_2) Λ)))
   (neither Σ L_1 P)
   -----------------------------------------------
   (δ _ Σ = [L_1 L_2] 0 (Σ⊓ Σ L_1 (¬/P P)))]
  ;; +
  [(where n_1 (@ Σ L_1))    (where n_2 (@ Σ L_2))
   -----------------------------------------------
   (δ _ Σ + [L_1 L_2] ,(+ (term n_1) (term n_2)) Σ)]
  [(where S_1 (@ Σ L_1))    (where S_2 (@ Σ L_2))
   (side-condition ,(or (•? (term S_1)) (•? (term S_2))))
   -----------------------------------------------
   (δ _ Σ + [L_1 L_2] (• ℤ (=/P + L_1 L_2)) Σ)]
  ;; -
  [(where n_1 (@ Σ L_1))    (where n_2 (@ Σ L_2))
   -----------------------------------------------
   (δ _ Σ - [L_1 L_2] ,(- (term n_1) (term n_2)) Σ)]
  [(where S_1 (@ Σ L_1))    (where S_2 (@ Σ L_2))
   (side-condition ,(or (•? (term S_1)) (•? (term S_2))))
   -----------------------------------------------
   (δ _ Σ - [L_1 L_2] (• ℤ (=/P - L_1 L_2)) Σ)]
  ;; *
  [(where n_1 (@ Σ L_1))    (where n_2 (@ Σ L_2))
   -----------------------------------------------
   (δ _ Σ * [L_1 L_2] ,(* (term n_1) (term n_2)) Σ)]
  [(where S_1 (@ Σ L_1))    (where S_2 (@ Σ L_2))
   (side-condition ,(or (•? (term S_1)) (•? (term S_2))))
   -----------------------------------------------
   (δ _ Σ * [L_1 L_2] (• ℤ (=/P * L_1 L_2)) Σ)]
  ;; /
  [(δ Λ Σ zero? [L_2] 1 Σ_1)
   -----------------------------------------------
   (δ L Σ / [L_1 L_2] (err L /) Σ_1)]
  [(δ Λ Σ zero? [L_2] 0 Σ_1)
   (where n_1 (@ Σ_1 L_1))    (where n_2 (@ Σ_1 L_2))
   -----------------------------------------------
   (δ L Σ / [L_1 L_2] ,(quotient (term n_1) (term n_2)) Σ_1)]
  [(δ Λ Σ zero? [L_2] 0 Σ_1)
   (where S_1 (@ Σ_1 L_1))    (where S_2 (@ Σ_1 L_2))
   (side-condition ,(or (•? (term S_1)) (•? (term S_2))))
   -----------------------------------------------
   (δ L Σ / [L_1 L_2] (• ℤ (=/P / L_1 L_2)) Σ_1)])

(define-metafunction SCPCF
  Σ⊓ : Σ L P -> Σ
  [(Σ⊓ (name Σ {_ ... [L ↦ (• _ ... P _ ...)] _ ...}) L P) Σ]
  [(Σ⊓ {any_1 ... [L ↦ (• T P_1 ...)] any_2 ...} L P)
   {any_1 ... [L ↦ (• T P_1 ... P)] any_2 ...}]
  [(Σ⊓ Σ _ _) Σ])

(module+ test
  (require rackunit)

  (define ans⊒?
    (match-lambda**
     [(x x) #t]
     [(`(• ,_ ,P ...) `(• ,_ ,Q ...))
      (subset? (list->set P) (list->set Q))]
     [(_ _) #f]))

  (define-syntax-rule (δ! O [V ...] A)
    (test-case (format "δ⟦~a, ~a⟧ = ~a" (term O) (term (V ...)) (term A))
      (define-values (Σ Ls)
        (values
         (for/list ([Vᵢ (list (term V) ...)] [i (in-naturals)])
           (term [,i ↦ ,Vᵢ]))
         (for/list ([_ (list (term V) ...)] [i (in-naturals)]) i)))
      (define anses (judgment-holds (δ Λ ,Σ O ,Ls any _) any))
      (check-equal? (length anses) 1)
      (check-true (ans⊒? (term A) (car anses)))))

  (define-syntax-rule (δ⊇ O [V ...] [A ...])
    (test-case (format "δ⟦~a, ~a⟧ ⊇ ~a" (term O) (term (V ...)) (term (A ...)))
      (define-values (Σ Ls)
        (values
         (for/list ([Vᵢ (list (term V) ...)] [i (in-naturals)])
           (term [,i ↦ ,Vᵢ]))
         (for/list ([_ (list (term V) ...)] [i (in-naturals)]) i)))
      (define reses (judgment-holds (δ Λ ,Σ O ,Ls any _) any))
      (check-true
       (for/and ([Aᵢ (term (A ...))])
         (for/or ([res (in-list reses)])
           (ans⊒? Aᵢ res))))))

  (define-syntax-rule (δ∋ O [V ...] A) (δ⊇ O [V ...] [A]))

  (δ! zero? [0] 1)
  (δ! zero? [42] 0)
  (δ⊇ zero? [(• ℤ)] (0 1))
  (δ! zero? [(• ℤ Zero?)] 1)
  (δ! zero? [(• ℤ (¬/P Zero?))] 0)
  (δ! + (42 43) 85)
  (δ! * (42 43) 1806)
  (δ! / (1 0) (err Λ /))
  (δ! / (7 3) 2)
  (δ⊇ / [(• ℤ) (• ℤ)] {(• ℤ) (err Λ /)})
  (δ! / [(• ℤ) (• ℤ Zero?)] (err Λ /))
  (δ! / [(• ℤ) (• ℤ (¬/P Zero?))] (• ℤ))
  (δ! > [42 43] 0)
  (δ! > [42 41] 1)
  (δ! > [42 42] 0)
  (δ! ≥ [42 42] 1)
  (δ! = [42 42] 1)
  (δ! = [42 43] 0)
  (δ! - [100 (• ℤ)] (• ℤ))
  (δ! / [1 100] 0)
  )
