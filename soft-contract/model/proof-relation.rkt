#lang racket/base

(provide (all-defined-out))

(require racket/match racket/set racket/list redex/reduction-semantics
         "lib.rkt" "syntax.rkt")

;; Might look tedious, but these would be generated in a real implementation

;; Strengthen path-condition `Γ` with both `S` and its negation.
;; Return `#f` if path-condition would be infeasible
(define-metafunction λ-sym
  MΓ+/- : M Γ V S -> (?Γ ?Γ)
  [(MΓ+/- M Γ V S)
   ,(let ([Γ_t (term (Γ+ Γ S))]
          [Γ_f (term (Γ+ Γ (@S not S)))])
      (case (term (MΓ⊢VS M Γ V S))
        [(✓) (term (,Γ_t  #f ))]
        [(✗) (term (#f   ,Γ_f))]
        [(?) (term (,Γ_t ,Γ_f))]))])

;; Strengthen path-condition `Γ` with whether `W` satisfies `o`.
;; Return `#f` if path-condition would be infeasible
(define-metafunction λ-sym
  MΓ+/-oW : M Γ o W -> (?Γ ?Γ)
  [(MΓ+/-oW M Γ o (name W (_ @ S)))
   ,(let ([Γ_t (term (Γ+ Γ (@S o S)))]
          [Γ_f (term (Γ+ Γ (@S not (@S o S))))])
      (case (term (MΓ⊢oW M Γ o W))
        [(✓) (term (,Γ_t  #f ))]
        [(✗) (term (#f   ,Γ_f))]
        [(?) (term (,Γ_t ,Γ_f))]))])

;; Check if value `W` represents truth under assumption `Γ`
(define-metafunction λ-sym
  MΓ⊢VS : M Γ V S -> R
  [(MΓ⊢VS M Γ V S) (first-R (⊢V V) (MΓ⊢S M Γ S))])

;; Check if symbolic value `S` evaluates to truth under assumption `Γ`
(define-metafunction λ-sym
  MΓ⊢S : M Γ S -> R
  [(MΓ⊢S M _ #f) ?]
  [(MΓ⊢S M _ e) !R
   (where !R (⊢e e))]
  [(MΓ⊢S M Γ e) !R
   (judgment-holds (∈ e_0 ,(set->list (Γ-props (term Γ)))))
   (where !R (e⊢e e_0 e))]
  [(MΓ⊢S M _ _) ?])

(define-metafunction λ-sym
  ⊢e : e -> R
  [(⊢e •) ?]
  [(⊢e 0) ✗]
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
  [(⊢oe integer? v) ✗]
  [(⊢oe procedure? (λ _ _)) ✓]
  [(⊢oe procedure? o) ✓]
  [(⊢oe procedure? v) ✗]
  [(⊢oe procedure? (add1 _)) ✗]
  [(⊢oe procedure? (not _)) ✗]
  [(⊢oe _ _) ?])

(define-metafunction λ-sym
  e⊢e : e e -> R
  [(e⊢e e e) ✓]
  [(e⊢e (not e _) e) ✗]
  [(e⊢e e_1 (not e_2)) (neg-R (e⊢e e_1 e_2))]
  [(e⊢e (o_1 e _) (o_2 e _)) (o⊢o o_1 o_2)]
  [(e⊢e _ _) ?])

(define-metafunction λ-sym
  o⊢o : o o -> R
  [(o⊢o o o) ✓]
  [(o⊢o not integer?) ✓]
  [(o⊢o integer? not) ?]
  [(o⊢o _ _) ✗])

;; Check if value `V` represents truth
(define-metafunction λ-sym
  ⊢V : V -> R
  [(⊢V ●) ?]
  [(⊢V ●-integer) ?]
  [(⊢V 0) ✗]
  [(⊢V _) ✓])

;; Check if value `W` satisfy operator `o` under assumptions `Γ`
(define-metafunction λ-sym
  MΓ⊢oW : M Γ o W -> R
  [(MΓ⊢oW M Γ o (V @ S)) (first-R (⊢oV o V) (MΓ⊢S M Γ (@S o S)))])

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
  [(⊢oV _ _) ✗])

;; Check if value `V` definitely contradicts symbol `S` and path condition `Γ`
;; `#f` is the conservative answer "maybe no".
(define-metafunction λ-sym
  spurious? : M Γ V S -> boolean
  [(spurious? M Γ 0 S)
   ,(or (equal? '✗ (term (MΓ⊢S M Γ (@S not S))))
        (equal? '✗ (term (MΓ⊢S M Γ (@S integer? S)))))]
  [(spurious? M Γ n S)
   ,(equal? '✗ (term (MΓ⊢S M Γ (@S integer? S))))]
  [(spurious? M Γ (Clo _ _ _ _) S)
   ,(equal? '✗ (term (MΓ⊢S M Γ (@S procedure? S))))]
  [(spurious? M Γ o S)
   ,(equal? '✗ (term (MΓ⊢S M Γ (@S procedure? S))))]
  [(spurious? _ ...) #f])

;; Strengthen path condition `Γ_1` with `Γ_2` or `#f` for provably spurious one
(define-metafunction λ-sym
  Γ⊓ : Γ Γ -> ?Γ
  [(Γ⊓ Γ Γ_1)
   ,(for/fold ([Γ* (term Γ)]) ([e (in-set (term Γ_1))])
      (and Γ*
           (match-let ([`(,?Γ ,_) (term (Γ+/-e ,Γ* ,e))])
             ?Γ)))])
