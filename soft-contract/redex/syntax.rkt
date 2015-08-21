#lang racket/base
(require racket/match racket/set redex/reduction-semantics racket/contract "lib.rkt")
(provide (all-defined-out))

(define-language L
  ;; Program and module
  [prog (d ... e)]
  [d (def x v)]

  ;; Expression
  [(e e*) v x (e e) (o¹ e) (o² e e) (if e e e) (ref x) (set! x e) err]
  [(x y z f g h) variable-not-otherwise-mentioned]
  [v (λ (x) e) b •]
  [b n]
  [(m n) integer]
  [o o¹ o²]
  [o¹ add1 o? o@]
  [o@ car cdr]
  [o? not integer? procedure? cons?]
  [o² = cons]
  [(?e ?e*) e #f]
  
  ;; Store & Environment & Value
  ; Store maps each address to a value set
  [(σ σ* σ**) (side-condition (name σ any) ((mmap/c α? V?) (term σ)))]
  ; Environment maps each variable to an address and its a canonical syntax piece
  [(ρ ρ* ρ**) (side-condition (name ρ any) ((map/c x? α?) (term ρ)))]
  ; Disjoint union set remembering equivalent subexpressions
  [(Γ Γ* Γ**) (side-condition (name Γ any) ((set/c e?) (term Γ)))]
  [(V V* V**) V! ●]
  [V! b (Clo x e ρ Γ) (Cons α α)]
  [(α β γ) any]
  [(W W* W**) (V @ ?e)]
  [?Γ Γ #f]
 
  ;; Evaluation answer
  [err (blm any)]
  [Vns V err]
  [Wns W err]
  [A α err]

  ;; Provability answer
  [R ✓+X ?]
  [✓+X ✓ X] ; definite answer

  ;; state
  [ς (E Γ σ τ Ξ M) (E Γ σ #f Ξ M)]
  [E (e ρ) W err]
  [κ (φ τ)]
  [φ (o [W ...] [e ...] ρ) (if e e ρ) (fn e ρ) (ar W) (rt Γ ?e) (set! α) tail]
  [(τ τ* τ**) (e ρ Γ)] ; stack address
  [(Ξ Ξ*) (side-condition (name Ξ any) ((mmap/c τ? κ?) (term Ξ)))]
  [(M M*) (side-condition (name M any) ((mmap/c e? M-rng?) (term M)))]
  [ςs (side-condition (name ςs any) ((set/c ς?) (term ςs)))]
  
  ;; state with shared widened stores
  [ξ (Cs σ Ξ M)]
  [(Cs Cs*) (side-condition (name Cs any) ((set/c C?) (term Cs)))]
  [C (E Γ τ) (E Γ #f)] ; configuration

  [xs (side-condition (name xs any) ((set/c x?) (term xs)))] ; variable set

  ;; Unimportant helpers
  [M-rng (?e Γ)])

(define e? (redex-match? L e))
(define ●? (redex-match? L ●))
(define V? (redex-match? L V))
(define Clo? (redex-match? L (Clo _ _ _ _)))
(define Cons? (redex-match? L (Cons _ _)))
(define α? (redex-match? L α))
(define x? (redex-match? L x))
(define W? (redex-match? L W))
(define τ? (redex-match? L τ))
(define κ? (redex-match? L κ))
(define M-rng? (redex-match? L M-rng))
(define M? (redex-match? L M))
(define Ξ? (redex-match? L Ξ))
(define C? (redex-match? L C))
(define Cs? (redex-match? L Cs))
(define ς? (redex-match? L ς))
(define ξ? (redex-match? L ξ))
(define σ? (redex-match? L σ))
(define prog? (redex-match? L prog))

(module+ test
  (require rackunit)
  (define-term ρ₁ {M+ [x ↦ 1] [y ↦ 2]})
  (define-term σ₁ {M+ [1 ↦ {S+ 1 2 3}] [2 ↦ {S+ 1 2 3}]})
  (define-term Γ₁ {S+ x y (not (car x)) (not (cdr z))})
  (check-true (redex-match? L ρ (term ρ₁)))
  (check-true (redex-match? L σ (term σ₁)))
  (check-true (redex-match? L Γ (term Γ₁))))

;; syntactic sugar
(define-metafunction L
  LET : (x e) e -> e
  [(LET (x e_x) e) ((λ (x) e) e_x)])
(define-metafunction L
  LET* : ([x e] ...) e -> e
  [(LET* () e) e]
  [(LET* ([x e_x] any ...) e) (LET [x e_x] (LET* (any ...) e))])
(define-metafunction L
  AND : e ... -> e
  [(AND) 1]
  [(AND e) e]
  [(AND e e* ...) (if e (AND e* ...) 0)])
(define-metafunction L
  OR : e ... -> e
  [(OR) 0]
  [(OR e) e]
  [(OR e e* ...) (if e 1 (OR e* ...))]) ; sloppy
(define-metafunction L
  COND : [e e] ... #:else e -> e
  [(COND #:else e) e]
  [(COND [e_1 e_2] any ...) (if e_1 e_2 (COND any ...))])

(define-metafunction L
  @* : ?e ?e -> ?e
  [(@* e_1 e_2) (e_1 e_2)]
  [(@* _ _) #f])

(define-metafunction L
  FV : e -> xs
  [(FV (λ (x) e)) (-- (FV e) {S+ x})]
  [(FV b) ∅]
  [(FV •) ∅]
  [(FV x) {S+ x}]
  [(FV (e_1 e_2)) (∪ (FV e_1) (FV e_2))]
  [(FV (o e ...)) (∪ (FV e) ...)]
  [(FV (if e ...)) (∪ (FV e) ...)]
  [(FV (ref _)) ∅]
  [(FV err) ∅]
  [(FV (set! x e)) (∪ {S+ x} (FV e))])

;; naive substitution
(define-metafunction L
  e/ : e x e -> e
  [(e/ (name v (λ (x) _)) x _) v]
  [(e/ (λ (z) e) x e*) (λ (z) (e/ e x e*))]
  [(e/ b _ _) b]
  [(e/ x x e) e]
  [(e/ z _ _) z]
  [(e/ (o e ...) x e*) (o (e/ e x e*) ...)]
  [(e/ (if e ...) x e*) (if (e/ e x e*) ...)]
  [(e/ (e ...) x e*) ((e/ e x e*) ...)]
  [(e/ (ref x) _ _) (ref x)]
  [(e/ err _ _) err])
(define-metafunction L
  Γ/ : Γ x e -> Γ
  [(Γ/ Γ x e*)
   ,(for/set ([e (in-set (term Γ))])
      (term (e/ ,e x e*)))])

(define-metafunction L
  ↓ : Γ xs -> Γ
  [(↓ Γ xs)
   ,(for/set ([e (in-set (term Γ))]
              #:when (subset? (term (FV ,e)) (term xs)))
      e)])

(module+ test
  (check-equal? (term (↓ Γ₁ {S+ x})) (term {S+ x (not (car x))}))
  (check-equal? (term (dom ρ₁)) (term {S+ x y}))
  (check-equal? (term (dom σ₁)) (term {S+ 1 2})))

;; primitive -> predicate
(define-metafunction L
  flat/c : o? -> V
  [(flat/c o?) ((Clo x (o? x) {} {}) :)])
(define-metafunction L
  neg/c : o? -> V
  [(neg/c o?) ((↓ x (not (o? x)) {} {}) :)])

(define-metafunction L
  Γ+ : Γ ?e -> Γ
  [(Γ+ Γ ⊘) Γ]
  [(Γ+ Γ e) ,(set-add (term Γ) (term e))])

;; Example terms
(define-term p1
  (LET* ([x •])
    (if (integer? x) (add1 x) 42)))

;; for debugging only
;; Compute the difference between 2 widened states
(define/contract (ξ-diff ξ₁ ξ₂)
  (ξ? ξ? . -> . (values Cs? σ? Ξ? M?))
  (match-define (list Cs₁ σ₁ Ξ₁ M₁) ξ₁)
  (match-define (list Cs₂ σ₂ Ξ₂ M₂) ξ₂)
  (values (set-subtract Cs₁ Cs₂)
          (mmap-diff σ₁ σ₂)
          (mmap-diff Ξ₁ Ξ₂)
          (mmap-diff M₁ M₂)))
