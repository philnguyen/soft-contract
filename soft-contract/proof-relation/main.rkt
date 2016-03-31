#lang typed/racket/base

(provide Γ⊢ₑₓₜ MΓ⊢V∈C MΓ⊢oW MΓ⊢s MΓ⊓ Γ+/-V Γ+/-W∋Ws
         plausible-ΓW? plausible-ΓE?
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

(: MΓ⊢V∈C : -M -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MΓ⊢V∈C M Γ W_v W_c)
  (match-define (-W¹ V e_v) W_v)
  (match-define (-W¹ C e_c) W_c)
  (first-R (p∋Vs C V) (MΓ⊢s M Γ (-?@ e_c e_v))))

(: MΓ⊢oW : -M -Γ -o -W¹ * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MΓ⊢oW M Γ p . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (first-R (apply p∋Vs p Vs)
           (MΓ⊢s M Γ (apply -?@ p ss))))

(: MΓ⊢s : -M -Γ -s → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MΓ⊢s M Γ s)
  (with-debugging/off ((ans) (MΓ*⊢s M {set (cons Γ s)}))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (define ss (show-s s))
    (printf "chk: ~a ⊢ ~a : ~a ~n" sΓ ss ans)
    (for ([sγ sγs])
      (printf "  - ~a~n" sγ))
    (printf "~n")))

(: MΓ*⊢s ([-M (℘ (Pairof -Γ -s))] [#:depth Natural] . ->* . -R))
;; Check if pair of ⟨path-condition, proposition⟩ is provable
;; This function inverts the path-condition up to finite depth if it can't
;; give a definite answer
(define (MΓ*⊢s M ps #:depth [d 5])
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
                              [✓-mt? (MΓ*⊢s M ps* #:depth (- d 1))]
                              [else (case (MΓ*⊢s M ps* #:depth (- d 1))
                                      [(✓)   '✓]
                                      [(✗ ?) '?])])]
                       [✓-mt?
                        (define ps* (invert-ps M ?s))
                        (cond [(equal? ps* ?s) '?]
                              [else
                               (case (MΓ*⊢s M ps* #:depth (- d 1))
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
                       [else (error 'MΓ*⊢s "wrong")])))
       (printf "~n"))]))

(: MΓ⊓ : -M -Γ -Γ → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (MΓ⊓ M Γ₀ Γ₁)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (define Γ₀*
    (for/fold ([Γ₀ : (Option -Γ) Γ₀]) ([φ₁ φs₁])
      (and Γ₀
           (case (MΓ⊢s M Γ₀ φ₁)
             [(✓ ?) (Γ+ Γ₀ φ₁)]
             [(✗)   #f]))))
  (match Γ₀*
    [(-Γ φs₀ as₀ γs₀) (-Γ φs₀ as₀ (∪ γs₀ γs₁))]
    [#f #f]))

(: Γ+/-V : -M -Γ -V -s → (Values (Option -Γ) (Option -Γ)))
;; Like `(Γ ⊓ s), V true` and `(Γ ⊓ ¬s), V false`, probably faster
(define (Γ+/-V M Γ V s)
  (Γ+/-R (first-R (⊢V V) (MΓ⊢s M Γ s)) Γ s))

(: Γ+/-W∋Ws : -M -Γ -W¹ -W¹ * → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `P(V…)` and `¬P(V…)`
(define (Γ+/-W∋Ws M Γ W-P . W-Vs)
  (match-define (-W¹ P s-p) W-P)
  (define-values (Vs s-vs) (unzip-by -W¹-V -W¹-s W-Vs))
  (define ψ (apply -?@ s-p s-vs))
  (define R (first-R (apply p∋Vs P Vs) (MΓ⊢s M Γ ψ)))
  (Γ+/-R R Γ ψ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Plausibility checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: plausible-ΓW? : -M -Γ -s (Listof (Pairof Var-Name -s)) -Γ -W → Boolean)
;; Check if returned value is plausible
(define (plausible-ΓW? M Γ₀ f bnds Γₐ Wₐ)
  (error "TODO"))

(: plausible-ΓE? : -M -Γ -s (Listof (Pairof Var-Name -s)) -Γ -blm → Boolean)
;; Check if propagated blame is plausible
(define (plausible-ΓE? M Γ₀ f bnds Γₐ blm)
  (error "TODO"))

(: plausible-rt? : -M -Γ -s (Listof (Pairof Var-Name -s)) -Γ -s → Boolean)
;; Checks if `Γ` under renaming `(f bnds)` can be a conjunct of `Γ₀`
;; - `#f` means a definite spurious return
;; - `#t` means a conservative plausible return
(define (plausible-rt? M Γ₀ f bnds Γ sₐ)
  (define m₀ (bnds->subst bnds))
  (define-values (mₑₑ mₑᵣ) (mk-subst m₀ f bnds sₐ))

  (define Γ*  (ensure-simple-consistency (Γ/ mₑₑ Γ )))
  (define Γ₀* (ensure-simple-consistency (Γ/ mₑᵣ Γ₀)))
  (define Γ₀** (and Γ* Γ₀* (MΓ⊓ M Γ₀* Γ*)))

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
