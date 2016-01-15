#lang racket/base
(require racket/match racket/set racket/contract/base redex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 1. Syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language λ-sym
  ;; λ-calculus plus:
  ;; - `set!`. Mutable variables are prefixed with `!` to obviate the need for an analysis.
  ;; - Primitives with arity 1.
  ;; - Static opaque values `ℓ`
  ;; - Contexts `l` for application and `set!` for blaming
  [e ::= v x (if e e e) (e e l) (set! !x e)]
  [v ::= b (λ (x) e) •]
  [• ::= (ℓ n)]
  [b ::= o n]
  [n ::= integer]
  [o ::= o? add1]
  [o? ::= procedure? integer? not] ;; all total predicates
  [!x ::= (side-condition (name !x variable) (regexp-match? #rx"!.+" (symbol->string (term !x))))]
  [l ::= variable] ; blame label
  [x y z ::= variable-not-otherwise-mentioned]
  [xs ::= (side-condition (name xs any) ((set/c symbol?) (term xs)))]

  ;; CEΓKS Machine
  ;; - Value store to handle `set!`
  ;; - No stack approximation for now
  [ς   ::= (E Γ κ σ) #|HACK|# Spurious]
  [E   ::= (e ρ) A]
  [A   ::= W blm]
  [blm ::= (blame l string)]
  
  ;; Runtime value
  ;; - An evaluated value has 2 parts:
  ;;   * Regular value `V`: familiar concrete values plus opaque ones of coarse types
  ;;   * Symbolic value `S`: if present, indicates that this value has been evaluated
  ;;     independent of mutable state. This steals the concept of `object` from Typed Racket,
  ;;     except it's generalized to all of `e`.
  [W ::= (V @ S)]
  [V ::= V-cnc V-opq]
  [S ::= e #f]
  [V-cnc ::= (Clo x e ρ Γ) b]
  [V-opq ::= ● ●-integer ●-procedure]
  
  ;; Path condition is conjunction of expressions known to have evaluated to truth
  [Γ ::= (side-condition (name Γ any) ((set/c values) (term Γ)))]
  [?Γ Γ #f]

  ;; Environment
  [ρ ::= (side-condition (name ρ any) ((hash/c x? α? #:flat? #t) (term ρ)))]

  ;; Store + value address
  [σ ::= (side-condition (name σ any) ((hash/c α? V? #:flat? #t) (term σ)))]
  [α ::= integer]

  ;; Stack frame and stack
  [φ ::= (φ.if e e ρ) (φ.ar e ρ l) (φ.fn W l) (φ.set! α) (φ.rt Γ S [x ↦ S])]
  [κ ::= (φ ...)]
  
  ;; Proof relation result
  [R  ::= !R ?]
  [!R ::= ✓ X])

(define x? (redex-match? λ-sym x))
(define α? (redex-match? λ-sym α))
(define S? (redex-match? λ-sym S))
(define V? (redex-match? λ-sym V))
(define b? (redex-match? λ-sym b))
(define φ.rt? (redex-match? λ-sym (φ.rt _ ...)))

(define-term ρ⊥ ,(hash))
(define-term σ⊥ ,(hash))
(define-term Γ⊤ ,(set))
(define-term κ₀ ())


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 2. Semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Load expression into initial program state
(define-metafunction λ-sym
  𝑰 : e -> ς
  [(𝑰 e) ((e ρ⊥) Γ⊤ κ₀ σ⊥)])

(define ->
  (reduction-relation
   λ-sym #:domain ς
   
   ;; Base stuff
   [--> ((x ρ) Γ κ σ)
        ((V @ S) Γ κ σ)
        Var
        (where V ,(hash-ref (term σ) (hash-ref (term ρ) (term x))))
        ; Reading from an asignable variable does not a refinable symbolic value
        (where S ,(if (redex-match? λ-sym !x (term x)) #f (term x)))]
   [--> ((b _) Γ κ σ)
        ((b @ b) Γ κ σ)
        Base]
   [--> (((λ (x) e) ρ) Γ κ σ)
        (((Clo x e ρ Γ) @ (λ (x) e)) Γ κ σ)
        Lam]
   [--> ((• ρ) Γ κ σ)
        ((● @ •) Γ κ σ)
        Sym]

   ;; Set!
   [--> (((set! x e) ρ) Γ (φ ...) σ)
        ((e ρ) Γ ((φ.set! α) φ ...) σ)
        Set-Push
        (where α ,(hash-ref (term ρ) (term x)))]
   [--> ((V @ _) Γ ((φ.set! α) φ ...) σ)
        ((1 @ 1) Γ (φ ...) ,(hash-set (term σ) (term α) (term V))) ; `1` as `unit`
        Set]

   ;; Conditional
   [--> (((if e e_1 e_2) ρ) Γ (φ ...) σ)
        ((e ρ) Γ ((φ.if e_1 e_2 ρ) φ ...) σ)
        If]
   [--> (W Γ ([φ.if e _ ρ] φ ...) σ)
        ((e ρ) Γ_1 (φ ...) σ)
        If-True
        (where (Γ_1 _) (Γ+/-W Γ W))]
   [--> (W Γ ([φ.if _ e ρ] φ ...) σ)
        ((e ρ) Γ_1 (φ ...) σ)
        If-False
        (where (_ Γ_1) (Γ+/-W Γ W))]

   ;; Application
   [--> (((e_f e_x l) ρ) Γ (φ ...) σ)
        ((e_f ρ) Γ ([φ.ar e_x ρ l] φ ...) σ)
        App]
   [--> (W Γ ([φ.ar e ρ l] φ ...) σ)
        ((e ρ) Γ ([φ.fn W l] φ ...) σ)
        App-Swap]
   [--> (W_x Γ ([φ.fn W_f l] φ ...) σ)
        ((e ρ_f*) Γ_f ([φ.rt Γ e_f [x ↦ e_x]] φ ...) σ_1)
        App-β
        (where (V_f @ e_f) W_f)
        (where (V_x @ e_x) W_x)
        (where (Clo x e ρ_f Γ_f) V_f)
        (where α ,(hash-count (term σ)))
        (where σ_1 ,(hash-set (term σ) (term α) (term V_x)))
        (where ρ_f* ,(hash-set (term ρ_f) (term x) (term α)))]
   [--> (W_x Γ ([φ.fn W_f l] φ ...) σ)
        (A Γ_a (φ ...) σ)
        App-δ
        (where (o @ _) W_f)
        (where (Γ_a A) (δ l Γ o W_x))]
   [--> (W_x Γ ([φ.fn W_f l] φ ...) σ)
        ((blame l "apply non-procedure") Γ_1 (φ ...) σ)
        App-Err
        (where (_ Γ_1) (Γ+/-oW Γ procedure? W_f))]
   [--> (W_x Γ ([φ.fn W_f l] φ ...) σ)
        ((● @ S_a) Γ_1 (φ ...) σ)
        App-●-TODO-havoc
        (where (● @ S_f) W_f)
        (where (_ @ S_x) W_x)
        (where S_a (@S S_f S_x)) ; unknown function assumed extensional by default
        (where (Γ_1 _) (Γ+/-oW Γ procedure? W_f))]

   ;; Error propagation within scope
   [--> (blm Γ (φ_0 φ ...) σ)
        (blm Γ () σ)
        Blm-Done
        (side-condition (not (ormap φ.rt? (term (φ_0 φ ...)))))]

   ;; Return/change context
   [--> ((V @ S) Γ ([φ.rt Γ_0 S_f [x ↦ S_x]] φ ...) σ)
        ((V @ S_a) Γ_1 (φ ...) σ)
        Rt-Val
        (where Γ_1 (rt-Γ Γ x Γ_0 S_x))
        (where S_a ,(and (term S) (term (@S S_f S_x))))]
   [--> (blm Γ (φ_0 ... [φ.rt Γ_0 S_f [x ↦ S_x]] φ ...) σ)
        (blm Γ_1 (φ ...) σ)
        Blm-Prop
        (side-condition (not (ormap φ.rt? (term (φ_0 ...)))))
        (where Γ_1 (rt-Γ Γ x Γ_0 S_x))]
   [--> (_ Γ ([φ.rt Γ_0 S_f [x ↦ S_x]] _ ...) _)
        Spurious
        Spurious
        (where #f (rt-Γ Γ x Γ_0 S_x))]))

;; Visualize program traces
(define (viz e) (traces -> (term (𝑰 ,e))))

;; Convert propositions `e` in Γ into propositions `[x/S_x]e` in Γ_0 then strengthen `Γ_0`
(define-metafunction λ-sym
  rt-Γ : Γ x Γ S -> ?Γ
  [(rt-Γ _ _ Γ_0 #f) Γ_0]
  [(rt-Γ Γ x Γ_0 e_x)
   (Γ⊓ Γ_0 Γ_arg)
   (where Γ_x ,(for/set ([e (in-set (term Γ))]
                         #:when (subset? (term (FV ,e)) (set (term x))))
                 e))
   (where Γ_arg ,(for/set ([e (in-set (term Γ_x))])
                   (term (e/ ,e x e_x))))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 3. Proof relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Primitives might look tedious, but these would be generated in a real implementation

;; Check if value `W` represents truth under assumption `Γ`
(define-metafunction λ-sym
  Γ⊢W : Γ W -> R
  [(Γ⊢W Γ (V @ S)) (first-R (⊢V V) (Γ⊢S Γ S))])

;; Check if symbolic value `S` evaluates to truth under assumption `Γ`
(define-metafunction λ-sym
  Γ⊢S : Γ S -> R
  [(Γ⊢S _ #f) ?]
  [(Γ⊢S _ e) !R
   (where !R (⊢e e))]
  [(Γ⊢S Γ e) !R
   (where {_ ... e_0 _ ...} ,(set->list (term Γ)))
   (where !R (e⊢e e_0 e))]
  [(Γ⊢S _ _) ?])

(define-metafunction λ-sym
  ⊢e : e -> R
  [(⊢e •) ?]
  [(⊢e 0) X]
  [(⊢e v) ✓]
  [(⊢e (o e _)) (⊢oe o e)]
  [(⊢e _) ?])

(define-metafunction λ-sym
  ⊢oe : o S -> R
  [(⊢oe _ #f) ?]
  [(⊢oe o? •) ?]
  [(⊢oe not e) (neg-R (⊢e e))]
  [(⊢oe integer? n) ✓]
  [(⊢oe integer? (add1 _)) ✓]
  [(⊢oe integer? (not _)) ✓]
  [(⊢oe integer? v) X]
  [(⊢oe procedure? (λ _ _)) ✓]
  [(⊢oe procedure? o) ✓]
  [(⊢oe procedure? v) X]
  [(⊢oe procedure? (add1 _)) X]
  [(⊢oe procedure? (not _)) X]
  [(⊢oe _ _) ?])

(define-metafunction λ-sym
  e⊢e : e e -> R
  [(e⊢e e e) ✓]
  [(e⊢e (not e _) e) X]
  [(e⊢e e_1 (not e_2)) (neg-R (e⊢e e_1 e_2))]
  [(e⊢e (o_1 e _) (o_2 e _)) (o⊢o o_1 o_2)]
  [(e⊢e _ _) ?])

(define-metafunction λ-sym
  o⊢o : o o -> R
  [(o⊢o o o) ✓]
  [(o⊢o not integer?) ✓]
  [(o⊢o integer? not) ?]
  [(o⊢o _ _) X])

;; Check if value `V` represents truth
(define-metafunction λ-sym
  ⊢V : V -> R
  [(⊢V ●) ?]
  [(⊢V ●-integer) ?]
  [(⊢V 0) X]
  [(⊢V _) ✓])

;; Check if value `W` satisfy operator `o` under assumptions `Γ`
(define-metafunction λ-sym
  Γ⊢oW : Γ o W -> R
  [(Γ⊢oW Γ o (V @ S)) (first-R (⊢oV o V) (Γ⊢S Γ (@S o S)))])

;; Return each (satisfiable) strengthened environment assuming `W` does and does not satisfy `o`
(define-metafunction λ-sym
  Γ+/-oW : Γ o W -> (?Γ ?Γ)
  [(Γ+/-oW Γ o (name W (_ @ S)))
   ,(case (term (Γ⊢oW Γ o W))
      [(✓) (term (Γ_t #f))]
      [(X) (term (#f Γ_f))]
      [(?) (term (Γ_t Γ_f))])
   (where Γ_t (Γ+ Γ (@S o S)))
   (where Γ_f (Γ+ Γ (@S not (@S o S))))])

(define-metafunction λ-sym
  Γ+/-W : Γ W -> (?Γ ?Γ)
  [(Γ+/-W Γ (name W (_ @ S)))
   ,(case (term (Γ⊢W Γ W))
      [(✓) (term (Γ_t #f))]
      [(X) (term (#f Γ_f))]
      [(?) (term (Γ_t Γ_f))])
   (where Γ_t (Γ+ Γ S))
   (where Γ_f (Γ+ Γ (@S not S)))])

(define-metafunction λ-sym
  Γ+/-e : Γ e -> (?Γ ?Γ)
  [(Γ+/-e Γ e) (Γ+/-W Γ (● @ e))])

(define-metafunction λ-sym
  ⊢oV : o V -> R
  [(⊢oV o? ●) ?]
  [(⊢oV integer? n) ✓]
  [(⊢oV integer? ●-integer) ✓]
  [(⊢oV not 0) ✓]
  [(⊢oV not ●-integer) ?]
  [(⊢oV procedure? (Clo _ _ _ _)) ✓]
  [(⊢oV procedure? o) ✓]
  [(⊢oV procedure? ●-procedure) ✓]
  [(⊢oV _ _) X])

;; Strengthen path condition `Γ_1` with `Γ_2` or `#f` for provably spurious one
(define-metafunction λ-sym
  Γ⊓ : Γ Γ -> ?Γ
  [(Γ⊓ Γ Γ_1)
   ,(for/fold ([Γ* (term Γ)]) ([e (in-set (term Γ_1))])
      (and Γ*
           (match-let ([`(,?Γ ,_) (term (Γ+/-e ,Γ* ,e))])
             ?Γ)))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4. Primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Might look tedious, but these would be generated in a real implementation

(define-metafunction λ-sym
  δ : l Γ o W -> (Γ A)
  [(δ _ Γ o? (name W (_ @ S)))
   (Γ (●-integer @ (@S o? S)))
   (where ? (Γ⊢oW Γ o? W))]
  [(δ _ Γ o? (name W (_ @ S)))
   (Γ (1 @ (@S o? S)))
   (where ✓ (Γ⊢oW Γ o? W))]
  [(δ _ Γ o? (name W (_ @ S)))
   (Γ (0 @ (@S o? S)))
   (where X (Γ⊢oW Γ o? W))]
  [(δ _ Γ add1 (_ @ n))
   (Γ (n_1 @ n_1))
   (where n_1 ,(+ 1 (term n)))]
  [(δ _ Γ add1 (name W (_ @ S)))
   (Γ_ok (●-integer @ (@S add1 S)))
   (where (Γ_ok _) (Γ+/-oW Γ integer? W))]
  [(δ l Γ add1 W)
   (Γ_bad (blame l "add1 non-integer"))
   (where (_ Γ_bad) (Γ+/-oW Γ integer? W))])

(define-metafunction λ-sym
  @S : S S -> S
  [(@S _ ... #f _ ...) #f]
  [(@S o •) (o • Λ)]
  [(@S add1 n) ,(add1 (term n))]
  [(@S integer? n) 1]
  [(@S integer? v) 0]
  [(@S procedure? n) 0]
  [(@S procedure? (add1 _)) 0]
  [(@S procedure? (λ _ _)) 1]
  [(@S procedure? o) 1]
  [(@S not 0) 1]
  [(@S not v) 0]
  [(@S not (not (not e l))) (not e Λ)] ; `not²` ≢ `id`, but `not³` ≡ `not`
  [(@S e_f e_x) (e_f e_x Λ)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5. (Uninteresting) helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (sloppy) Substitution
(define-metafunction λ-sym
  e/ : e x e -> e
  [(e/ x x e) e]
  [(e/ y x e) y]
  [(e/ (λ (x) e) x _) (λ (x) e)]
  [(e/ (λ (y) e) x e_x) (λ (y) (e/ e x e_x))]
  [(e/ v _ _) v]
  [(e/ (if e ...) x e_x) (if (e/ e x e_x) ...)]
  [(e/ (e ... l) x e_x) ((e/ e x e_x) ... l)]
  [(e/ (set! x _) x e)
   ,(error 'e/ "asignable variable ~a" (term x))]
  [(e/ (set! !x e) x e_x) (set! !x (e/ e x e_x))])

(define-metafunction λ-sym
  FV : e -> xs
  [(FV x) ,(set (term x))]
  [(FV (λ (x) e)) ,(set-remove (term (FV e)) (term x))]
  [(FV (if e_0 e_1 e_2)) ,(set-union (term (FV e_0)) (term (FV e_1)) (term (FV e_2)))]
  [(FV (e_f e_x _)) ,(set-union (term (FV e_f)) (term (FV e_x)))]
  [(FV (set! x e)) ,(set-add (term (FV e)) (term x))]
  [(FV _) ,(set)])

;; Select the first definite answer
(define-metafunction λ-sym
  first-R : R ... -> R
  [(first-R) ?]
  [(first-R ? R ...) (first-R R ...)]
  [(first-R R _ ...) R])

;; Negate satisfiability answer
(define-metafunction λ-sym
  neg-R : R ... -> R
  [(neg-R ✓) X]
  [(neg-R X) ✓]
  [(neg-R ?) ?])

(define-metafunction λ-sym
  Γ+ : Γ S -> Γ
  [(Γ+ Γ #f) Γ]
  [(Γ+ Γ e) ,(set-add (term Γ) (term e))])

(define-metafunction λ-sym
  -let : ([x e]) e e ... -> e
  [(-let ([x e_x]) e_0 e ...) ((λ (x) (-begin e_0 e ...)) e_x Λ)])

(define-metafunction λ-sym
  -begin : e e ... -> e
  [(-begin e) e]
  [(-begin e_0 e ...)
   (-let ([□ e_0]) (-begin e ...))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(module+ test

  (define-term e₁
    (-let ([!x 42])
          (-begin
           (set! !x 43))
          (add1 !x ℓ₁)))

  (define-term e₂
    (-let ([f (ℓ 0)])
       (if (f 1 ℓ₀)
           (if (f 1 ℓ₁) 42 43) ; should reach 42 only
           (if (f 1 ℓ₂) 44 45)))) ; should reach 45 only

  (viz (term e₂)))
