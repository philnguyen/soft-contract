#lang typed/racket/base

(provide MΓ⊢V∈C MΓ⊢oW MΓ⊢s Γ+/-V Γ+/-W∋Ws
         #;plausible-return? #;plausible-blame?
         plausible-pc? plausible-index? plausible-indices
         (all-from-out "local.rkt"))

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "local.rkt"
         "ext.rkt")

(: MΓ⊢V∈C : -M -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MΓ⊢V∈C M Γ W_v W_c)
  (with-debugging/off
    ((ans)
     (match-define (-W¹ V v) W_v)
     (match-define (-W¹ C c) W_c)
     (first-R (p∋Vs C V) (MΓ⊢s M Γ (-?@ c v))))
    (printf "~a ⊢ ~a ∈ ~a : ~a~n" (show-Γ Γ) (show-W¹ W_v) (show-W¹ W_c) ans)))

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
  (with-debugging/off
    ((R)
     (cond
       [s
        (match (φs⊢e (-Γ-facts Γ) s)
          ['? (ext-prove M Γ s)]
          [R R])]
       [else '?]))
    (when s
      (match-define (-Γ φs _ γs) Γ)
      (for ([φ φs]) (printf "~a~n" (show-φ φ)))
      (for ([γ γs])
        (match-define (-γ _ bnd blm?) γ)
        (printf "~a ; blm?~a~n" (show-binding bnd) (and blm? #t))
        (printf "-----------------------------------------~a~n" R)
        (printf "~a~n~n" (show-e s))))
    ))

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

(: plausible-pc? : -M -Γ → Boolean)
(define plausible-pc? ext-plausible-pc?)

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
