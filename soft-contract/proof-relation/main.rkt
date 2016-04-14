#lang typed/racket/base

(provide MΓ⊢V∈C MΓ⊢oW MΓ⊢s Γ+/-V Γ+/-W∋Ws
         plausible-return? plausible-blame? plausible-index? plausible-indices
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
  (with-debugging/off
    ((R)
     (first-R (apply p∋Vs p Vs)
              (MΓ⊢s M Γ (apply -?@ p ss))))
    (printf "~a ⊢ ~a ~a : ~a~n" (show-Γ Γ) (show-o p) (map show-W¹ Ws) R)))

(: MΓ⊢s : -M -Γ -s → -R)
;; Check if `s` is provable in `Γ`
(define (MΓ⊢s M Γ s)
  (with-debugging/off ((ans) (if s (⊢cfg M (inj-cfg Γ s)) '?))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (define ss (show-s s))
    (printf "chk: ~a ⊢ ~a : ~a ~n" sΓ ss ans)
    (for ([sγ sγs])
      (printf "  - ~a~n" sγ))
    (printf "~n")))

(define (⊢cfg [M : -M] [cfg : -cfg]) (⊢cfgs M {set cfg}))

(: ⊢cfgs ([-M (℘ -cfg)] [#:depth Natural] . ->* . -R))
(define (⊢cfgs M cfgs #:depth [d 5])
  (cond
    [(<= d 0) '?]
    [else
     (define-values (✓s ✗s ?s) (partition-cfgs cfgs))
     (define ✓-mt? (set-empty? ✓s))
     (define ✗-mt? (set-empty? ✗s))
     (define ?-mt? (set-empty? ?s))

     (with-debugging/off
       ((ans)
        (cond
          [?-mt? (cond [✗-mt? '✓] [✓-mt? '✗] [else '?])]
          [else
           (cond [✗-mt?
                  (define cfgs* (invert-cfgs M cfgs))
                  (cond
                    [(equal? cfgs* cfgs) '?]
                    [✓-mt? (⊢cfgs M cfgs* #:depth (- d 1))]
                    [else (case (⊢cfgs M cfgs* #:depth (- d 1))
                            [(✓)   '✓]
                            [(✗ ?) '?])])]
                 [✓-mt?
                  (define cfgs* (invert-cfgs M cfgs))
                  (cond
                    [(equal? cfgs* cfgs) '?]
                    [else (case (⊢cfgs M cfgs* #:depth (- d 1))
                            [(✗)   '✗]
                            [(✓ ?) '?])])]
                 [else '?])]))
       (printf "worlds:~n")
       (for ([ctx ✓s])
         (match-define (-cfg (-ctx φs _ _) e) cfg)
         (printf "  - ~a ⊢ ~a : ✓~n" (set-map φs show-e) (show-e e)))
       (for ([ctx ✗s])
         (match-define (-cfg (-ctx φs _ _) e) cfg)
         (printf "  - ~a ⊢ ~a : ✗~n" (set-map φs show-e) (show-e e)))
       (for ([ctx ?s])
         (match-define (-cfg (-ctx φs _ _) e) cfg)
         (printf "  - ~a ⊢ ~a : ?~n" (set-map φs show-e) (show-e e)))
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

(: plausible-return? : -M -Γ -binding -Γ -W → Boolean)
;; Check if returned value is plausible
(define (plausible-return? M Γₑᵣ bnd Γₑₑ Wₑₑ)
  (match-define (-W Vs sₑₑ) Wₑₑ)
  (define-values (mₑₑ mₑᵣ sₑᵣ)
    (let ([m₀ (bnds->subst bnd)])
      (mk-subst m₀ bnd sₑₑ)))
  (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ Γₑₑ)))
  (define Γₑᵣ₁ (ensure-simple-consistency (Γ/ mₑᵣ Γₑᵣ)))
  (define Γₑᵣ₂ (and Γₑᵣ₁ Γₑᵣ₊ (Γ⊓ Γₑᵣ₁ Γₑᵣ₊)))
  (and Γₑᵣ₂ (implies sₑᵣ (plausible-W/M? M (inj-cfg Γₑᵣ₂ sₑᵣ) Vs))))

(: plausible-blame? : -M -Γ -binding -Γ -blm → Boolean)
;; Check if propagated blame is plausible
(define (plausible-blame? M Γₑᵣ bnd Γₑₑ blm)
  (define-values (mₑₑ mₑᵣ sₑᵣ)
    (let ([m₀ (bnds->subst bnd)])
      (mk-subst m₀ bnd #f)))
  (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ Γₑₑ)))
  (define Γₑᵣ₁ (and Γₑᵣ₊ (Γ⊓ Γₑᵣ Γₑᵣ₊)))
  (match-define (-blm l+ lo _ _) blm)
  (and Γₑᵣ₁ (implies sₑᵣ (plausible-blm/M? M (inj-cfg Γₑᵣ₁ sₑᵣ) l+ lo))))

(: plausible-W/M? ([-M -cfg (Listof -V)] [#:depth Natural] . ->* . Boolean))
(define (plausible-W/M? M cfg Vs #:depth [d 5])
  (cond
    [(<= d 0) #t]
    [else
     (match-define (-cfg (-ctx φs _ _) s) cfg)
     (and (plausible-W? φs Vs s)
          (for/or : Boolean ([cfg* (invert-cfg M cfg)])
            (plausible-W/M? M cfg* Vs #:depth (- d 1))))]))

(: plausible-blm/M? ([-M -cfg Mon-Party Mon-Party] [#:depth Natural] . ->* . Boolean))
;; Check if it's plausible that function call at symbol `s` has raised blame `blm`
(define (plausible-blm/M? M cfg l+ lo #:depth [d 5])
  (with-debugging/off
    ((ans)
     (match-define (-cfg (-ctx _ γʰs _) s) cfg)
     (cond
       [(<= d 0) #t]
       [(-v? s) #f]
       ;; plausible if path-condition witnessed blame from `s`
       [(for/or : Boolean ([γʰ γʰs])
          (match γʰ
            [(-γʰ (-γ _ bnd (-blm (== l+) (== lo) _ _)) _)
             (equal? s (binding->fargs bnd))]
            [_ #f]))
        #t]
       ;; implausible if path-condition witnessed successful return from `s`
       [(for/or : Boolean ([γʰ γʰs])
          (match γʰ
            [(-γʰ (-γ _ bnd #f) _)
             (equal? s (binding->fargs bnd))]
            [_ #f]))
        #f]
       [else
        (for/or : Boolean ([cfg* (invert-cfg M cfg)])
          (if (equal? cfg* cfg)
              #t
              (plausible-blm/M? M cfg* l+ lo #:depth (- d 1))))]))
    (match-define (-cfg (-ctx φs γʰs _) s) cfg)
    (define γs (map/set -γʰ-tail γʰs))
    (define Γ (-Γ φs (hash) γs))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: partition-cfgs : (℘ -cfg) → (Values (℘ -cfg) (℘ -cfg) (℘ -cfg)))
;; Paritition proof configurations into provable, refutable, and don't know
(define (partition-cfgs cfgs)
  (define-set ✓s : -cfg)
  (define-set ✗s : -cfg)
  (define-set ?s : -cfg)
  (for ([cfg cfgs])
    (match-define (-cfg (-ctx φs _ _) e) cfg)
    (case (es⊢e φs e)
      [(✓) (✓s-add! cfg)]
      [(✗) (✗s-add! cfg)]
      [(?) (?s-add! cfg)]))
  (values ✓s ✗s ?s))

(: Γ+/-R : -R -Γ -s → (Values (Option -Γ) (Option -Γ)))
;; Given `s`'s satisfiability in `Γ`, strengthen `Γ` both ways. `#f` represents a bogus path condition.
(define (Γ+/-R R Γ s)
  (case R
    [(✓) (values (Γ+ Γ s) #f)]
    [(✗) (values #f       (Γ+ Γ (-not s)))]
    [(?) (values (Γ+ Γ s) (Γ+ Γ (-not s)))]))

(: plausible-index? : -M -Γ -W¹ Natural → Boolean)
(define (plausible-index? M Γ W i)
  (case (MΓ⊢oW M Γ 'integer? W)
    [(✓ ?)
     (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
     (case (MΓ⊢oW M Γ '= W Wᵢ)
       [(✗) #f]
       [else #t])]
    [else #f]))

(: plausible-indices : -M -Γ -W¹ Natural Natural → (Listof Natural))
(define (plausible-indices M Γ W lo hi)
  (for*/list : (Listof Natural) ([i (in-range lo hi)]
                                 #:when (exact-nonnegative-integer? i) ; hack for TR
                                 #:when (plausible-index? M Γ W i))
    i))
