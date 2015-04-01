#lang racket/base
(provide (all-defined-out))
(require
 redex/reduction-semantics racket/match racket/port racket/system racket/string racket/function
 racket/list
 "lib.rkt" "lang.rkt" "tc.rkt" "proof-system.rkt")

(define-metafunction SCPCF
  translate-Σ : Σ -> (any ...)
  [(translate-Σ (name Σ {[L ↦ S] ...}))
   (φ ... ...)
   (where ((φ ...) ...) ((assert-L-S Σ L S) ...))])

(define-metafunction SCPCF
  declare-Σ : Σ -> (decl ...)
  [(declare-Σ {[L ↦ S] ...})
   ,(filter values (term ((declare (ℓ L) (tc-S S)) ...)))])

[define-metafunction SCPCF
  assert-L-S : Σ L S -> (φ ...)
  [(assert-L-S _ L n) {(= (ℓ L) n)}]
  [(assert-L-S _ L (• ℤ P ...))
   ,(filter values (term ((assert-L-P L P) ...)))]
  [(assert-L-S Σ L (case T [L_x ↦ L_a] ...))
   ,(for*/list ([tail (in-list (tails (term ([L_x ↦ L_a] ...))))]
                #:when (and (cons? tail) (cons? (cdr tail)))
                [L_x↦L_a (in-value (car tail))]
                [L_y↦L_b (in-list (cdr tail))])
      (match-define `(,L_x ↦ ,L_a) L_x↦L_a)
      (match-define `(,L_y ↦ ,L_b) L_y↦L_b)
      (term (⇒ (assert-eq ℤ Σ ,L_x ,L_y)
               (assert-eq T Σ ,L_a ,L_b))))]
  [(assert-L-S _ _ _) {}]]

(define-metafunction SCPCF
  assert-L-P : L P -> φ or #f
  [(assert-L-P L (λ (X : ℤ) (zero? X _))) (= (ℓ L) 0)]
  [(assert-L-P L (λ (X : ℤ) (= X (O² E ... _) _)))
   (= (ℓ L) ((⦃O⦄ O²) (⦃E⦄ E) ...))]
  [(assert-L-P L (λ (X : ℤ) (O² X E _))) ((⦃O⦄ O²) (ℓ L) (⦃E⦄ E))]
  [(assert-L-P L P) #f
   (side-condition (printf "ignore translation of ~a to Z3~n" (term P)))])

(define-metafunction SCPCF
  ℓ : L -> X
  [(ℓ L) ,(string->symbol (format "L-~a" (term L)))])

(define-metafunction SCPCF
  →L : X -> L
  [(→L X) ,(match (symbol->string (term X))
             [(regexp #rx"L-(.+)" (list _ (? string? s))) (string->number s)])])

(define-metafunction SCPCF
  ⦃E⦄ : E -> t
  [(⦃E⦄ n) n]
  [(⦃E⦄ (↓ ℤ L)) (ℓ L)])

(define-metafunction SCPCF
  ⦃O⦄ : O -> any
  [(⦃O⦄ ≥) >=]
  [(⦃O⦄ ≤) <=]
  [(⦃O⦄ O²) O²])

(define-metafunction SCPCF
  declare : X T -> decl or #f
  [(declare X ℤ) (declare-const X Int)]
  [(declare _ _) #f])

(define-metafunction SCPCF
  query : (decl ...) (φ ...) φ -> R
  [(query (decl ...) (φ ...) ψ) ✓
   (side-condition
    (regexp-match? #rx"^unsat" (term (call (decl ... (assert φ) ... (assert (not ψ)) (check-sat))))))]
  [(query (decl ...) (φ ...) ψ) !
   (side-condition
    (regexp-match? #rx"^unsat" (term (call (decl ... (assert φ) ... (assert ψ) (check-sat))))))]
  [(query _ _ _) ?])

(define-metafunction SCPCF
  call : (any ...) -> string
  [(call (any ...))
   ,(let ()
      (define req (string-join (map (curry format "~a") (term (any ...))) "\n"))
      (define res
        (with-output-to-string
          (λ () (system (format "echo \"~a\" | z3 -in -smt2" req)))))
      (log-debug "call:~n~a~nres:~n~a~n" req res)
      res)])

(define-metafunction SCPCF
  query/model : Σ -> (any ...)
  [(query/model (name Σ {[L ↦ S] ...}))
   (decl ... (assert φ) ... ... (check-sat) (get-model))
   (where (decl ...) (declare-Σ Σ))
   (where ((φ ...) ...) ((assert-L-S Σ L S) ...))])

(define-metafunction SCPCF
  model/z3 : Σ -> Σ or #f
  [(model/z3 Σ)
   ,(match (term (call (query/model Σ)))
      [(regexp #rx"^sat(.*)" (list _ (? string? s)))
       (match (with-input-from-string s read)
         [(list 'model lines ...)
          (for/fold ([Σ (term Σ)]) ([line (in-list lines)])
            (match-define `(define-fun ,(? symbol? L) () ,_ ,e) line)
            (term (!! ,Σ [(→L ,L) ↦ ,(eval e)])))])]
      [_ #f])])

(define-metafunction SCPCF
  model/Σ : Σ -> Σ
  [(model/Σ (name Σ {[L ↦ _] ...})) {[L ↦ (inst/L Σ L)] ...}])

(define-metafunction SCPCF
  inst/L : Σ L -> S
  [(inst/L (name Σ {_ ... [L ↦ (• ℤ P ...)] _ ...}) L)
   (inst/n 0 Σ L)]
  [(inst/L Σ L) (@ Σ L)])

(define-metafunction SCPCF
  inst/n : n Σ L -> n
  [(inst/n n Σ L) n
   (where #f (refutes Σ L (λ (x : ℤ) (= x n Λ))))]
  [(inst/n n Σ L) n_1
   (where #t (refutes Σ L (λ (x : ℤ) (= x n Λ))))
   (where n_1 ,(- (random 2000) 1000))])

;; Translate (syntactic) equality to Z3
(define-metafunction SCPCF
  assert-eq : T Σ L L -> φ
  [(assert-eq _ _ L L) True]
  [(assert-eq ℤ _ L_1 L_2) (= (ℓ L_1) (ℓ L_2))]
  [(assert-eq T Σ L_1 L_2)
   (assert-eq/S T Σ (@ Σ L_1) (@ Σ L_2))])
(define-metafunction SCPCF
  assert-eq/S : T Σ S S -> φ
  [(assert-eq/S ℤ _ n_1 n_2) ,(if (= (term n_1) (term n_2)) 'True 'False)]
  [(assert-eq/S (ℤ → T) Σ (case T [L_x ↦ L_a] ...) (case T [L_y ↦ L_b] ...))
   (∧ ,@(for*/list ([L_x↦L_a (in-list (term ([L_x ↦ L_a] ...)))]
                    [L_y↦L_b (in-list (term ([L_y ↦ L_b] ...)))])
          (match-define `(,L_x ↦ ,L_a) L_x↦L_a)
          (match-define `(,L_y ↦ ,L_b) L_y↦L_b)
          (term (⇒ (assert-eq ℤ Σ ,L_x ,L_y) (assert-eq T Σ ,L_a ,L_b)))))]
  [(assert-eq/S (T_x → T) Σ (λ (X : T_x) L_1) (λ (X : T_x) L_2))
   (assert-eq T Σ L_1 L_2)]
  [(assert-eq/S ((T_a → T_b) → T) Σ (λ (X : T_x) (L_1 (X L_2))) (λ (X : T_x) (L_3 (X L_4))))
   (∧ (assert-eq T_a Σ L_2 L_4) (assert-eq (T_b → T) Σ L_1 L_3))]
  [(assert-eq/S T Σ
                (λ (X : T_X) (λ (Y : T_Y) (((↓ _ L_1) X) Y)))
                (λ (X : T_X) (λ (T : T_Y) (((↓ _ L_2) X) Y))))
   (assert-eq T Σ L_1 L_2)]
  [(assert-eq/S T Σ (• T P ...) S) True
   (where _ ,(printf "assert-eq/S ~a: omit (= ~a ~a)~n" (term T) (term (• T P ...)) (term S)))]
  [(assert-eq/S T Σ S (• T P ...)) True
   (where _ ,(printf "assert-eq/S ~a: omit (= ~a ~a)~n" (term T) (term (• T P ...)) (term S)))]
  [(assert-eq/S T Σ S_1 S_2) False
   (where _ ,(printf "assert-eq/S ~a: not equal: ~a, ~a~n" (term T) (term S_1) (term S_2)))])

;;; Macros for simplifying Z3 formulas

(define-metafunction SCPCF
  ∧ : φ ... -> φ
  [(∧ _ ... False _ ...) False]
  [(∧ φ ... True ψ ...) (∧ φ ... ψ ...)]
  [(∧) True]
  [(∧ φ) φ]
  [(∧ φ ...) (and φ ...)])

(define-metafunction SCPCF
  ∨ : φ ... -> φ
  [(∨ _ ... True _ ...) True]
  [(∨ φ ... False ψ ...) (∨ φ ... ψ ...)]
  [(∨) False]
  [(∨ φ) φ]
  [(∨ (not φ) ψ) (⇒ φ ψ)]
  [(∨ φ ...) (or φ ...)])

(define-metafunction SCPCF
  ⇒ : φ φ -> φ
  [(⇒ φ False) (not φ)]
  [(⇒ φ True) True]
  [(⇒ False φ) True]
  [(⇒ True φ) φ]
  [(⇒ (not φ) (not ψ)) (⇒ ψ φ)]
  [(⇒ φ ψ) (=> φ ψ)])



(module+ test
  (require rackunit)
  (define-term Σ
    {[0 ↦ 1]
     [1 ↦ (• ℤ (λ (x : ℤ) (< x 3 Λ)))]
     [2 ↦ (• ℤ (λ (x : ℤ) (= x (+ (↓ ℤ 0) (↓ ℤ 1) Λ) Λ)))]
     [3 ↦ 42]
     [4 ↦ (case ℤ [0 ↦ 1] [2 ↦ 3])]})
  (define-term Σ₁
    {[a ↦ 1]
     [b ↦ 2]
     [c ↦ (case (ℤ → ℤ) [d ↦ e] [f ↦ g])]
     [d ↦ (• ℤ)]
     [e ↦ (case ℤ)]
     [f ↦ (• ℤ)]
     [g ↦ (case ℤ)]})
  (term (declare-Σ Σ))
  (term (translate-Σ Σ))
  (term (translate-Σ Σ₁))

  #;(let ([f (• (ℤ → (ℤ → ℤ)))]
      [a (• ℤ)]
      [b (• ℤ)]
      [c (• ℤ)])
  (=> (= a b)
      (= ((f a) c) ((f b) c))))
  (define-term Σ₂
    {[f ↦ (case (ℤ → ℤ) [a ↦ fa] [b ↦ fb])]
     [a ↦ (• ℤ)]
     [b ↦ (• ℤ (λ (X : ℤ) (= X (↓ ℤ a) Λ)))]
     [c ↦ (• ℤ)]
     [fa ↦ (case ℤ [c ↦ fac])]
     [fb ↦ (case ℤ [c ↦ fbc])]
     [fac ↦ (• ℤ)]
     [fbc ↦ (• ℤ)]})
  (term (translate-Σ Σ₂))

  #;(let ([f (• (ℤ → ((ℤ → ℤ) → ℤ)))]
        [a (• ℤ)]
        [b (• ℤ)]
        [g (λ (X : ℤ) (+ 1 X Λ))]
        [h (λ (Y : ℤ) (+ Y 1 Λ))])
    (=> (= a b)
        (= ((f a) g) ((f b) h))))
  )
