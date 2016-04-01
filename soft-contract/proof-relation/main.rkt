#lang typed/racket/base

(provide Γ⊢ₑₓₜ MΓ⊢V∈C MΓ⊢oW MΓ⊢s Γ+/-V Γ+/-W∋Ws
         plausible-return? plausible-blame?
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
  (match-define (-W¹ V v) W_v)
  (match-define (-W¹ C c) W_c)
  (first-R (p∋Vs C V) (MΓ⊢s M Γ (-?@ c v))))

(: MΓ⊢oW : -M -Γ -o -W¹ * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MΓ⊢oW M Γ p . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (first-R (apply p∋Vs p Vs)
           (MΓ⊢s M Γ (apply -?@ p ss))))

(: MΓ⊢s : -M -Γ -s → -R)
;; Check if `s` is provable in `Γ`
(define (MΓ⊢s M Γ s)
  (with-debugging/off ((ans) (M⊢Γs M {set (cons Γ s)}))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (define ss (show-s s))
    (printf "chk: ~a ⊢ ~a : ~a ~n" sΓ ss ans)
    (for ([sγ sγs])
      (printf "  - ~a~n" sγ))
    (printf "~n")))

(: M⊢Γs ([-M (℘ (Pairof -Γ -s))] [#:depth Natural] . ->* . -R))
;; Check if all pairs of ⟨Γ, s⟩ are provable.
;; This function inverts the path-condition up to finite depth
(define (M⊢Γs M ps #:depth [d 5])
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
                              [✓-mt? (M⊢Γs M ps* #:depth (- d 1))]
                              [else (case (M⊢Γs M ps* #:depth (- d 1))
                                      [(✓)   '✓]
                                      [(✗ ?) '?])])]
                       [✓-mt?
                        (define ps* (invert-ps M ?s))
                        (cond [(equal? ps* ?s) '?]
                              [else
                               (case (M⊢Γs M ps* #:depth (- d 1))
                                 [(✗)   '✗]
                                 [(✓ ?) '?])])]
                       [else '?])]))
       (printf "worlds:~n")
       (for ([p ✓s])
         (match-define (cons Γ s) p)
         (printf "  - ~a ⊢ ~a : ✓~n" (show-Γ Γ) (show-s s)))
       (for ([p ✗s])
         (match-define (cons Γ s) p)
         (printf "  - ~a ⊢ ~a : ✗~n" (show-Γ Γ) (show-s s)))
       (for ([p ?s])
         (match-define (cons Γ s) p)
         (printf "  - ~a ⊢ ~a : ?~n" (show-Γ Γ) (show-s s)))
       (printf "~n"))]))

(: Γ+/-V : -M -Γ -V -s → (Values (Option -Γ) (Option -Γ)))
;; Like `(Γ ⊓ s), V true` and `(Γ ⊓ ¬s), V false`, probably faster
(define (Γ+/-V M Γ V s)
  (Γ+/-R (first-R (⊢V V) (MΓ⊢s M Γ s)) Γ s))

(: Γ+/-W∋Ws : -M -Γ -W¹ -W¹ * → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `P(V…)` and `¬P(V…)`
(define (Γ+/-W∋Ws M Γ Wₚ . Wᵥₛ)
  (match-define (-W¹ P p) Wₚ)
  (define-values (Vs vs) (unzip-by -W¹-V -W¹-s Wᵥₛ))
  (define ψ (apply -?@ p vs))
  (define R (first-R (apply p∋Vs P Vs) (MΓ⊢s M Γ ψ)))
  (Γ+/-R R Γ ψ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Plausibility checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: plausible-return? : -M -Γ -s (Listof (Pairof Var-Name -s)) -Γ -W → Boolean)
;; Check if returned value is plausible
(define (plausible-return? M Γₑᵣ f bnds Γₑₑ Wₑₑ)
  (match-define (-W Vs sₑₑ) Wₑₑ)
  (define-values (mₑₑ mₑᵣ sₑᵣ)
    (let ([m₀ (bnds->subst bnds)])
      (mk-subst m₀ f bnds sₑₑ)))
  (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ Γₑₑ)))
  (define Γₑᵣ₁ (ensure-simple-consistency (Γ/ mₑᵣ Γₑᵣ)))
  (define Γₑᵣ₂ (and Γₑᵣ₁ Γₑᵣ₊ (Γ⊓ Γₑᵣ₁ Γₑᵣ₊)))
  (and Γₑᵣ₂ (plausible-W/M? M Γₑᵣ₂ Vs sₑᵣ)))

(: plausible-blame? : -M -Γ -s (Listof (Pairof Var-Name -s)) -Γ -blm → Boolean)
;; Check if propagated blame is plausible
(define (plausible-blame? M Γₑᵣ f bnds Γₑₑ blm)
  (define-values (mₑₑ mₑᵣ sₑᵣ)
    (let ([m₀ (bnds->subst bnds)])
      (mk-subst m₀ f bnds #f)))
  (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ Γₑₑ)))
  (define Γₑᵣ₁ (and Γₑᵣ₊ (Γ⊓ Γₑᵣ Γₑᵣ₊)))
  (match-define (-blm l+ lo _ _) blm)
  (and Γₑᵣ₁ (plausible-blm/M? M Γₑᵣ₁ sₑᵣ l+ lo)))

(: plausible-W/M? ([-M -Γ (Listof -V) -s] [#:depth Natural] . ->* . Boolean))
(define (plausible-W/M? M Γ Vs s #:depth [d 5])
  (cond
    [(<= d 0) #t]
    [else
     (and (plausible-W? Γ Vs s)
          (for/or : Boolean ([p (invert-Γ M Γ)])
            (match-define (cons Γ* m) p)
            (define s* (and s ((e/map m) s)))
            (plausible-W/M? M Γ* Vs s* #:depth (- d 1))))]))

(: plausible-blm/M? ([-M -Γ -s Mon-Party Mon-Party] [#:depth Natural] . ->* . Boolean))
;; Check if it's plausible that function call at symbol `s` has raised blame `blm`
(define (plausible-blm/M? M Γ s l+ lo #:depth [d 5])
  (define γs (-Γ-tails Γ))
  (with-debugging
    ((ans)
     (cond
       [(<= d 0) #t]
       [(-v? s) #f]
       [(for/or : Boolean ([γ γs])
          (match γ
            [(-γ _ f bnds (-blm (== l+) (== lo) _ _))
             (define s* (fbnds->fargs f bnds))
             (printf "blm: comparing ~a to ~a~n" (show-s s) (show-s s*))
             (equal? s s*)]
            [_ #f]))
        #t]
       [(for/or : Boolean ([γ γs])
          (match γ
            [(-γ _ f bnds #f)
             (define s* (fbnds->fargs f bnds))
             (printf "val: comparing ~a to ~a~n" (show-s s) (show-s s*))
             (equal? s s*)]
            [_ #f]))
        #f]
       [else
        (for/or : Boolean ([p (invert-Γ M Γ)])
          (match-define (cons Γ* m) p)
          (or (equal? Γ* Γ)
              (let ([s* (and s ((e/map m) s))])
                (plausible-blm/M? M Γ* s* l+ lo #:depth (- d 1)))))]))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (printf "plausible-blm? ~a ⊢ (blm ~a ~a) @ ~a : ~a~n" sΓ l+ lo (show-s s) ans)
    (printf "evaled: ~a~n"
            (for/list : (Listof Sexp) ([γ γs] #:unless (-γ-blm γ))
              `(,(show-γ γ) ↦ ,(show-s (γ->fargs γ)))))
    (printf "blamed: ~a~n"
            (for/list : (Listof Sexp) ([γ γs] #:when (-γ-blm γ))
              `(,(show-γ γ) ↦ ,(show-s (γ->fargs γ)))))
    (printf "where:~n")
    (for ([s sγs]) (printf "  - ~a~n" s))
    (printf "~n")))


#|
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
|#


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
