#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics racket/set "lib.rkt")

(define-language SCPCF
  [E A V X (if E E E) (E E) (O¹ E L′) (O² E E L′)]
  [V (• T L′) (λ (X : T) E) n]
  [A (↓ T L) Err]
  [Err (err L′ O)]
  [O O¹ O²]
  [O¹ zero?]
  [O² + - * / = > < ≤ ≥]
  [P (λ (X : T) E)]
  [(T T′) ℤ (T → T)]
  [Σ {[L ↦ S] ...}]
  [S (• T P ...) (λ (X : T) E) n (case T [L ↦ L] ...)]
  [n integer]
  [n+ (side-condition (name n+ n) (> (term n+) 0))]
  [(X Y Z) variable-not-otherwise-mentioned]
  [L natural L′]
  [L′ X]
  [C hole (if C E E) (C E) (A C) (O A ... C E ... L)]
  [Γ {[X ↦ T] ...}]
  [δ↓ S Err]
  [ς (E Σ)]
  [Ls {L ...}]
  ;; Z3 stuff
  [τ Int]
  [decl (declare-const X τ) (declare-fun X (τ ...) τ)]
  [(φ ψ) True False (and φ ...) (or φ ...) (=> φ φ) (not φ) (O² t t) (>= t t) (<= t t)]
  [t n (O² t t) X]
  [q (decl ... (assert φ) ... (check-sat))
     (decl ... (assert φ) ... (check-sat) (get-model))]
  [R ✓ ! ?]
  ;; opaque functions
  [Sλ• (• (T → T))
       (case T [L ↦ L] ...)
       (λ (X : T) (↓ T L))
       (λ (X : (T_1 → T_2))
         (λ (Y : T_3)
           (((↓ ((T_1 → T_2) → (T_2 → T_4)) L) X) Y)))
       (λ (X : (T′ → T)) ((↓ T L) (X (↓ T′ L))))])

(define E? (redex-match? SCPCF E))
(define •? (redex-match? SCPCF (• T _ ...)))
(define ς? (redex-match? SCPCF ς))
(define T? (redex-match? SCPCF T))
(define hole? (redex-match? SCPCF hole))
(define X? (redex-match? SCPCF X))
(define A? (redex-match? SCPCF A))
(define Σ? (redex-match? SCPCF Σ))

;; Use judgment-form just to by friendly to type-setting
(define-judgment-form SCPCF
  #:contract (∉dom L Σ [L ...])
  #:mode     (∉dom O I I      )
  [(∉dom ,(+ 1 (apply max -1 (filter integer? (term (L_i ... L_j ...)))))
         {[L_i ↦ _] ...}
         {L_j ...})])

(define-metafunction SCPCF
  +X : T -> X
  [(+X ℤ) x]
  [(+X (ℤ → ℤ)) f]
  [(+X _) g])

(define-term Zero? (λ (x : ℤ) (zero? x Λ)))

(define-metafunction SCPCF
  ¬/P : P -> P
  [(¬/P (λ (X : T) E)) (λ (X : T) (zero? E Λ))])

(define-metafunction SCPCF
  =/P : O L L -> P
  [(=/P O L_1 L_2) (λ (x : ℤ) (= x (O (↓ ℤ L_1) (↓ ℤ L_2) Λ) Λ))])

;; Non-capture-avoiding substitution. Use with care.
(define-metafunction SCPCF
  // : E X E -> E
  [(// (name V (λ (X : T) _)) X _) V]
  [(// (λ (X : T) E) Y E_Y) (λ (X : T) (// E Y E_Y))]
  [(// X X E) E]
  [(// X _ _) X]
  [(// (if E ...) X E_X) (if (// E X E_X) ...)]
  [(// (E_f E_x) Y E_Y) ((// E_f Y E_Y) (// E_x Y E_Y))]
  [(// (O E ... L) X E_X) (O (// E X E_X) ... L)]
  [(// E _ _) E])

(define-metafunction SCPCF
  holes : E -> Ls
  [(holes (if E ...)) (∪ (holes E) ...)]
  [(holes (E_f E_x)) (∪ (holes E_f) (holes E_x))]
  [(holes (O E ... L)) (∪ (holes E) ...)]
  [(holes (λ (X : T) E)) (holes E)]
  [(holes (• T L′)) {L′}]
  [(holes _) {}])

;; Compute labels for concrete program portions
(define-metafunction SCPCF
  labs/Σ : Σ E -> {L ...}
  [(labs/Σ Σ (↓ T L)) (labs/Σ Σ E)
   (where (λ _ E) (@ Σ L))]
  [(labs/Σ Σ (λ _ E)) (labs/Σ Σ E)]
  [(labs/Σ Σ (if E ...)) (∪ (labs/Σ Σ E) ...)]
  [(labs/Σ Σ (E_f E_x)) (∪ (labs/Σ Σ E_f) (labs/Σ Σ E_x))]
  [(labs/Σ Σ (O E ... L)) (∪ {L} (labs/Σ Σ E) ...)]
  [(labs/Σ _ _) {}])

(define-metafunction SCPCF
  labs : E -> {L ...}
  [(labs (λ _ E)) (labs E)]
  [(labs (if E ...)) (∪ (labs E) ...)]
  [(labs (E_f E_x)) (∪ (labs E_f) (labs E_x))]
  [(labs (O E ... L)) (∪ {L} (labs E) ...)]
  [(labs _) {}])

(define-metafunction SCPCF
  FV : E -> {X ...}
  [(FV (λ (X : T) E)) (-- (FV E) {X})]
  [(FV X) {X}]
  [(FV (if E ...)) (∪ (FV E) ...)]
  [(FV (O E ... L)) (∪ (FV E) ...)]
  [(FV (E E_x)) (∪ (FV E) (FV E_x))]
  [(FV _) {}])

;; Count occurrences of X in E
(define-metafunction SCPCF
  count-X : X E -> n
  [(count-X X X) 1]
  [(count-X X (if E ...)) ,(apply + (term ((count-X X E) ...)))]
  [(count-X X (O E ... L)) ,(apply + (term ((count-X X E) ...)))]
  [(count-X X (λ (X : T) _)) 0]
  [(count-X X (λ (Z : T) E)) (count-X X E)]
  [(count-X X E) 0])

(define-relation SCPCF
  conc? ⊆ V
  [(conc? n)]
  [(conc? (λ (X : T) _))])

(module+ test
  (require rackunit)

  (define-syntax-rule (check-labs E {L ...})
    (check-equal? (list->set (term (labs E)))
                  {set (term L) ...}))

  (check-labs 42 {})
  (check-labs (+ 1 2 a) {a})
  (check-labs (((• ((ℤ → ℤ) → (ℤ → ℤ)) f)
                (λ (n : ℤ) (if (= n 0 l) 100 0))) 0)
              {l}))
