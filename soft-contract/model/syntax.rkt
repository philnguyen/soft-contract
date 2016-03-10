#lang racket/base

(provide (all-defined-out))
(require racket/list racket/match racket/set racket/contract redex/reduction-semantics "lib.rkt")

(define-extended-language λ-sym mt
  ;; λ-calculus plus:
  ;; - set!, with asignable variables prefixed by "!" to obviate an analysis pass
  ;; - Primitives with arity 1.
  ;; - Static opaque values `ℓ`
  ;; - Contexts `l` for application and `set!` for blaming
  [e  ::= v x (if e e e) (e e l) (set! !x e)]
  [v  ::= b (λ (x) e) •]
  [•  ::= (side-condition (name • variable) (regexp-match? #rx"•.+" (symbol->string (term •))))]
  [b  ::= o n]
  [n  ::= integer]
  [o  ::= o? add1]
  [o? ::= procedure? integer? not] ;; all total predicates
  [l  ::= #|blame label|# (side-condition (name l variable) (regexp-match? #rx"ℓ.+" (symbol->string (term l))))]
  [!x ::= (side-condition (name !x variable) (regexp-match? #rx"!.+" (symbol->string (term !x))))]
  [x y z ::= (side-condition (name x variable-not-otherwise-mentioned) (not (•? (term x))))]
  [xs ::= (side-condition (name xs any) ((set/c symbol?) (term xs)))]

  ;; Machine (local) configuration without global stores
  [ς ::= (E Γ κ) #|HACK|# Spurious]
  [E ::= (e ρ) A]
  [A ::= W blm]
  [blm ::= (blame l string)]

  ;; Path-condition is set (conjunction) of:
  ;; - expression known to have evaluated to truth
  ;; - path-condition pointer, locating a possible conjunction of this path-condition
  [Γ  ::= (side-condition (name Γ any) (Γ? (term Γ)))]
  [?Γ ::= Γ #f]
  ;; A reference to the rest of the path condition is an address to an evaluation result
  ;; along with the result syntax in the current block and renaming information
  [γ ::= (τ e [x ↦ e])]
  
  ;; Environment
  [ρ ::= (side-condition (name ρ any) ((hash/c x? α? #:flat? #t) (term ρ)))]
  
  ;; Runtime value
  ;; - A value `W` has 2 parts:
  ;;   * Regular value `V`: can be either concrete or opaque
  ;;   * Symbolic value `S`: if present, indicates that this value has been evaluated
  ;;     independent of mutable state. This steals the concept of `object` from Typed Racket,
  ;;     except it's generalized to all of `e`.
  [W ::= (V @ S)]
  [V ::= V-cnc V-opq]
  [S ::= e #f]
  [V-cnc ::= (Clo x e ρ Γ) b]
  [V-opq ::= ● ●-integer ●-procedure]

  ;; Store + value address
  [σ ::= (side-condition (name σ any) ((hash/c α? (set/c V?) #:flat? #t) (term σ)))]
  [α ::= variable]

  ;; A stack consists of standard frame, except the tail is an address to
  ;; the rest of the stack
  [κ ::= (φ ... τ)]
  [φ ::= (if e e ρ) (e ρ l) (W l) (set! x α) (havoc W S) (rt Γ S [x ↦ S])]
  [τ ::= (side-condition (name τ variable) (regexp-match? #rx"τ.+" (symbol->string (term τ))))]

  ;; Stack store maps stack address to possible resuming contexts
  [Ξ ::= (side-condition (name Ξ any) ((hash/c τ? (set/c κ?) #:flat? #t) (term Ξ)))]

  ;; Result store maps stack address to possible result and path condition
  [M ::= (side-condition (name M any) ((hash/c τ? (set/c Ans?) #:flat? #t) (term M)))]
  [Ans ::= (side-condition (name Ans any) (Ans? (term Ans)))]
  
  ;; Proof relation result
  [R  ::= !R ?]
  [!R ::= ✓ ✗])

(define x? (redex-match? λ-sym x))
(define α? (redex-match? λ-sym α))
(define S? (redex-match? λ-sym S))
(define V? (redex-match? λ-sym V))
(define b? (redex-match? λ-sym b))
(define e? (redex-match? λ-sym e))
(define τ? (redex-match? λ-sym τ))
(define κ? (redex-match? λ-sym κ))
(define A? (redex-match? λ-sym A))
(define γ? (redex-match? λ-sym γ))
(define !x? (redex-match? λ-sym !x))
(define •? (redex-match? λ-sym •))
(define ℓ? (redex-match? λ-sym ℓ))
(define-struct/contract Γ
  ([canonical (hash/c e? e? #:flat? #t)] ; just equality, but contains hint for simplifying which expression to which
   [props (set/c e?)]
   [rests (set/c γ?)])
  #:transparent)
(define-struct/contract Ans ([path-condition Γ?] [ans A?]) #:transparent)

(define-values (α α⁻¹) (unique-name 'α))
(define-values (τ τ⁻¹) (unique-name 'τ))

(define-metafunction λ-sym
  ->τ : e ρ Γ -> τ
  [(->τ e ρ Γ) ,(τ (term (e ρ Γ)))])

(define-metafunction λ-sym
  ->α : any ... -> α
  [(->α any ...) ,(α (term (any ...)))])

(define-term ∅ ,(set))
(define-term ⊥ρ ,(hash))
(define-term ⊥σ ,(hash))
(define-term ⊥Ξ ,(hash))
(define-term ⊥M ,(hash))
(define-term ⊤Γ ,(make-Γ (hash) (term ∅) (term ∅)))

(define-metafunction λ-sym
  e/ : e x e -> e
  [(e/ x x e) e]
  [(e/ (λ (x) e) x _) (λ (x) e)]
  [(e/ (λ (y) e) x e_x) (λ (y) (e/ e x e_x))]
  [(e/ (if e ...) x e_x) (if (e/ e x e_x) ...)]
  [(e/ (e ... l) x e_x) ((e/ e x e_x) ... l)]
  [(e/ (set! x _) x e) ,(error 'e/ "asignable variable ~a" (term x))]
  [(e/ (set! x e) x e_x) (set! x (e/ e x e_x))]
  [(e/ e _ _) e])

(define-metafunction λ-sym
  FV : e -> xs
  [(FV x) ,(set (term x))]
  [(FV (λ (x) e)) ,(set-remove (term (FV e)) (term x))]
  [(FV (if e_0 e_1 e_2)) ,(set-union (term (FV e_0)) (term (FV e_1)) (term (FV e_2)))]
  [(FV (e_f e_x _)) ,(set-union (term (FV e_f)) (term (FV e_x)))]
  [(FV (set! x e)) ,(set-add (term (FV e)) (term x))]
  [(FV _) ∅])

(define-metafunction λ-sym
  FV-Γ : Γ -> xs
  [(FV-Γ Γ)
   ,(set-union
     (for/fold ([acc {set}]) ([(k v) (Γ-canonical (term Γ))])
       (set-union acc (term (FV ,k))))
     (for/fold ([acc {set}]) ([e (Γ-props (term Γ))])
       (set-union acc (term (FV ,e))))
     (for/fold ([acc {set}]) ([γ (Γ-rests (term Γ))])
       (match-define `(,τ ,e [,x ↦ ,e_x]) γ)
       (set-union acc (term (FV ,e_x)))))])

;; Select the first definite answer
(define-metafunction λ-sym
  first-R : R ... -> R
  [(first-R) ?]
  [(first-R ? R ...) (first-R R ...)]
  [(first-R R _ ...) R])

;; Negate satisfiability answer
(define-metafunction λ-sym
  neg-R : R ... -> R
  [(neg-R ✓) ✗]
  [(neg-R ✗) ✓]
  [(neg-R ?) ?])

(define-metafunction λ-sym
  M@ : M τ -> any #|setof Ans|#
  [(M@ M τ) ,(hash-ref (term M) (term τ) set)])

(define-metafunction λ-sym
  Ξ@ : Ξ τ -> any #|setof _|#
  [(Ξ@ Ξ τ) ,(hash-ref (term Ξ) (term τ) set)])

(define-metafunction λ-sym
  σ@ : σ α -> any #|setof V|#
  [(σ@ σ α) ,(hash-ref (term σ) (term α))])

(define-metafunction λ-sym
  ρ@ : ρ x -> α
  [(ρ@ ρ x) ,(hash-ref (term ρ) (term x))])

(define-metafunction λ-sym
  Γ+ : Γ S -> Γ
  [(Γ+ Γ e)
   ,(make-Γ (Γ-canonical (term Γ))
            (set-add (Γ-props (term Γ)) (term e))
            (Γ-rests (term Γ)))]
  [(Γ+ Γ #f) Γ])

;; Represent the expression using the lexically farthest variables possible
(define-metafunction λ-sym
  canonicalize : Γ e -> e
  [(canonicalize Γ e) ,(hash-ref (Γ-canonical (term Γ)) (term x) (λ () (term e)))])

;; Rename free occurrences of `x` to `x_1` in `Γ`
(define-metafunction λ-sym
  Γ/ : Γ x x -> Γ
  [(Γ/ Γ x x_1)
   ,(let ()
      (define e->e
        (for/hash ([(k v) (Γ-canonical (term Γ))])
          (values k (term (e/ ,v x x_1)))))
      (define props
        (for/set ([e (Γ-props (term Γ))]) (term (e/ ,e x x_1))))
      (define rests
        (for/set ([γ (Γ-rests (term Γ))])
          (match-define `(,τ ,e [,x ↦ ,e_x]) γ)
          `(,τ ,e [,x ↦ ,(term (e/ ,e_x x x_1))])))
      (make-Γ e->e props rests))])

;; Invalidate everything `Γ` knows about `x`
(define-metafunction λ-sym
  invalidate : Γ x -> Γ
  [(invalidate Γ x)
   ,(let ()
      (define (has-x? e)
        (set-member? (term (FV ,e)) (term x)))
      (define e->e
        (for/hash ([(k v) (Γ-canonical (term Γ))] #:unless (has-x? k))
          (values k v)))
      (define props
        (for/set ([e (Γ-props (term Γ))] #:unless (has-x? e)) e))
      (define rests
        (for*/set ([γ (Γ-rests (term Γ))]
                   [e_x (in-value (second (third γ)))]
                   #:unless (has-x? e_x))
          γ))
      (make-Γ e->e props rests))])

;; Invalidate everything `Γ` knows about mutable variables
(define-metafunction λ-sym
  invalidate-muts : Γ -> Γ
  [(invalidate-muts Γ)
   ,(let ()
      (define (drop? e)
        (ormap !x? (set->list (term (FV ,e)))))
      (define e->e
        (for/hash ([(k v) (Γ-canonical (term Γ))] #:unless (drop? k))
          (values k v)))
      (define props
        (for/set ([e (Γ-props (term Γ))] #:unless (drop? e)) e))
      (define rests
        (for*/set ([γ (Γ-rests (term Γ))]
                   [e_x (in-value (second (third γ)))]
                   #:unless (drop? e_x))
          γ))
      (make-Γ e->e props rests))])

(define-metafunction λ-sym
  bind : Γ x S -> Γ
  [(bind Γ x S)
   ,(make-Γ (hash-set (Γ-canonical (term Γ_1)) (term x) (term S))
            (Γ-props (term Γ_1))
            (Γ-rests (term Γ_1)))
   ;; Generate fresh name `x_1` for old value of `x`
   (where x_1 ,(variable-not-in (set->list (term (FV-Γ Γ))) (term x)))
   (where Γ_1 (Γ/ Γ x x_1))])

(define-metafunction λ-sym
  ⊔ : any any any_v -> any
  [(⊔ any_m any_k any_v)
   ,(hash-update (term any_m) (term any_k) (λ (s) (set-add s (term any_v))) set)])

(define-metafunction λ-sym
  ⊔/m : any any -> any
  [(⊔/m any_m1 any_m2)
   ,(for/fold ([m (term any_m1)]) ([(k vs) (term any_m2)])
      (hash-update m k (λ (s) (set-union s vs)) set))])

;; Smart constructor for application of symbolic values with some simplifications
(define-metafunction λ-sym
  @S : S S -> S
  [(@S _ ... #f _ ...) #f]
  [(@S o •) (o • ℓΛ)]
  [(@S add1 n) ,(add1 (term n))]
  [(@S integer? n) 1]
  [(@S integer? v) 0]
  [(@S procedure? n) 0]
  [(@S procedure? (add1 _)) 0]
  [(@S procedure? (λ _ _)) 1]
  [(@S procedure? o) 1]
  [(@S not 0) 1]
  [(@S not v) 0]
  [(@S not (not (not e l))) (not e l)] ; `not²` ≢ `id`, but `not³` ≡ `not`
  [(@S e_f e_x) (e_f e_x ℓΛ)])

(define-metafunction λ-sym
  -let : ([x e]) e e ... -> e
  [(-let ([x e_x]) e_0 e ...) ((λ (x) (-begin e_0 e ...)) e_x ℓΛ)])

(define-metafunction λ-sym
  -begin : e e ... -> e
  [(-begin e) e]
  [(-begin e_0 e ...)
   (-let ([□ e_0]) (-begin e ...))])
