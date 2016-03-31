#lang typed/racket/base

(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢s MσΓ⊓ Γ+/-V Γ+/-W∋Ws
         plausible-W? plausible-rt?
         (all-from-out "local.rkt")
         (all-from-out "inversion.rkt"))

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "local.rkt"
         "inversion.rkt")

(: MσΓ⊢V∈C : -M -σ -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W¹ V e_v) W_v)
  (match-define (-W¹ C e_c) W_c)
  (first-R (p∋Vs C V) (MσΓ⊢s M σ Γ (-?@ e_c e_v))))

(: MσΓ⊢oW : -M -σ -Γ -o -W¹ * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (first-R (apply p∋Vs p Vs)
           (MσΓ⊢s M σ Γ (apply -?@ p ss))))

(: MσΓ⊢s : -M -σ -Γ -s → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢s M σ Γ s)
  (with-debugging/off ((ans) (MσΓ*⊢s M σ {set (cons Γ s)}))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (define ss (show-s s))
    (printf "chk: ~a ⊢ ~a : ~a ~n" sΓ ss ans)
    (for ([sγ sγs])
      (printf "  - ~a~n" sγ))
    (printf "~n")))

(: MσΓ*⊢s ([-M -σ (℘ (Pairof -Γ -s))] [#:depth Natural] . ->* . -R))
;; Check if pair of ⟨path-condition, proposition⟩ is provable
;; This function inverts the path-condition up to finite depth if it can't
;; give a definite answer
(define (MσΓ*⊢s M σ ps #:depth [d 5])
  (cond
    [(<= d 0) '?]
    [else
     (define-values (✓s ✗s ?s) (partition-Γs ps))
     (define ✓-mt? (set-empty? ✓s))
     (define ✗-mt? (set-empty? ✗s))
     (define ?-mt? (set-empty? ?s))

     (with-debugging/off
       ((ans)
        (cond
          [?-mt? (cond [✗-mt? '✓]
                       [✓-mt? '✗]
                       [else '?])]
          [else  (cond [✗-mt?
                        (define ps* (invert-ps M ?s))
                        (cond [(equal? ps* ?s) '?]
                              [✓-mt? (MσΓ*⊢s M σ ps* #:depth (- d 1))]
                              [else (case (MσΓ*⊢s M σ ps* #:depth (- d 1))
                                      [(✓)   '✓]
                                      [(✗ ?) '?])])]
                       [✓-mt?
                        (define ps* (invert-ps M ?s))
                        (cond [(equal? ps* ?s) '?]
                              [else
                               (case (MσΓ*⊢s M σ ps* #:depth (- d 1))
                                 [(✗)   '✗]
                                 [(✓ ?) '?])])]
                       [else '?])]))
       (printf "worlds:~n")
       (for ([p ps])
         (match-define (cons Γ s) p)
         (printf "  ~a ⊢ ~a : ~a~n"
                 (show-Γ Γ)
                 (show-s s)
                 (cond [(∋ ✓s p) '✓]
                       [(∋ ✗s p) '✗]
                       [(∋ ?s p) '?]
                       [else (error 'MσΓ*⊢s "wrong")])))
       (printf "~n"))]))

(: MσΓ⊓ : -M -σ -Γ -Γ → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (MσΓ⊓ M σ Γ₀ Γ₁)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (define Γ₀*
    (for/fold ([Γ₀ : (Option -Γ) Γ₀]) ([φ₁ φs₁])
      (and Γ₀
           (case (MσΓ⊢s M σ Γ₀ φ₁)
             [(✓ ?) (Γ+ Γ₀ φ₁)]
             [(✗)   #f]))))
  (match Γ₀*
    [(-Γ φs₀ as₀ γs₀) (-Γ φs₀ as₀ (∪ γs₀ γs₁))]
    [#f #f]))

(: Γ+/-V : -M -σ -Γ -V -s → (Values (Option -Γ) (Option -Γ)))
;; Like `(Γ ⊓ s), V true` and `(Γ ⊓ ¬s), V false`, probably faster
(define (Γ+/-V M σ Γ V s)
  (Γ+/-R (first-R (⊢V V) (MσΓ⊢s M σ Γ s)) Γ s))

(: Γ+/-W∋Ws : -M -σ -Γ -W¹ -W¹ * → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `P(V…)` and `¬P(V…)`
(define (Γ+/-W∋Ws M σ Γ W-P . W-Vs)
  (match-define (-W¹ P s-p) W-P)
  (define-values (Vs s-vs) (unzip-by -W¹-V -W¹-s W-Vs))
  (define ψ (apply -?@ s-p s-vs))
  (define R (first-R (apply p∋Vs P Vs) (MσΓ⊢s M σ Γ ψ)))
  (Γ+/-R R Γ ψ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Plausibility checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: plausible-rt? : -M -σ -Γ -s (Listof (Pairof Var-Name -s)) -Γ -s → Boolean)
;; Checks if `Γ` under renaming `(f bnds)` can be a conjunct of `Γ₀`
;; - `#f` means a definite spurious return
;; - `#t` means a conservative plausible return
(define (plausible-rt? M σ Γ₀ f bnds Γ sₐ)
  (define m₀ (bnds->subst bnds))
  (define-values (mₑₑ mₑᵣ) (mk-subst m₀ f bnds sₐ))

  (define Γ*  (ensure-simple-consistency (Γ/ mₑₑ Γ )))
  (define Γ₀* (ensure-simple-consistency (Γ/ mₑᵣ Γ₀)))
  (define Γ₀** (and Γ* Γ₀* (MσΓ⊓ M σ Γ₀* Γ*)))

  #;(begin ; debugging
    (printf "plausible? ~a [~a ~a] ~a [~a]~n"
            (show-Γ Γ₀)
            (show-s f)
            (for/list : (Listof Sexp) ([bnd bnds]) `(,(car bnd) ↦ ,(show-s (cdr bnd))))
            (show-Γ Γ)
            (show-s sₐ))
    (printf "  would-be conjunction: ~a~n" (and Γ* (show-Γ Γ*)))
    (printf "  would-be path-cond: ~a~n~n" (and Γ₀** (show-Γ Γ₀**))))

  (and Γ₀** #t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Γ+/-R : -R -Γ -s → (Values (Option -Γ) (Option -Γ)))
;; Given `s`'s satisfiability in `Γ`, strengthen `Γ` both ways. `#f` represents a bogus path condition.
(define (Γ+/-R R Γ s)
  (case R
    [(✓) (values (Γ+ Γ s) #f)]
    [(✗) (values #f       (Γ+ Γ (-not s)))]
    [(?) (values (Γ+ Γ s) (Γ+ Γ (-not s)))]))
