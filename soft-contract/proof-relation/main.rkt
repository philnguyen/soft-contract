#lang typed/racket/base

(provide MΓ⊢V∈C MΓ⊢oW MΓ⊢s Γ+/-V MΓ+/-oW with-Γ+/-
         plausible-return? plausible-return?/cheap plausible-index? plausible-indices
         (all-from-out "local.rkt" "widen.rkt"))

(require racket/match
         racket/set
         racket/bool
         syntax/parse/define
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "local.rkt"
         "ext.rkt"
         "widen.rkt")

(: MΓ⊢V∈C : -M -σ -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W¹ V v) W_v)
  (match-define (-W¹ C c) W_c)
  (with-debugging/off
    ((ans)
     (first-R (p∋Vs σ C (V+ σ V (predicates-of Γ v)))
              (match V
                [(-● ps)
                 (define Γ*
                   (for/fold ([Γ : -Γ Γ]) ([p ps])
                     (Γ+ Γ (-?@ p v))))
                 (MΓ⊢s M Γ* (-?@ c v))]
                [_ (MΓ⊢s M Γ (-?@ c v))])))
    (when (and (-Clo? V))
      (printf "~a ⊢ ~a ∈ ~a : ~a~n~n" (show-Γ Γ) (show-W¹ W_v) (show-W¹ W_c) ans))))

(: MΓ⊢oW : -M -σ -Γ -o -W¹ * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MΓ⊢oW M σ Γ p . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (with-debugging/off
    ((R)
     (first-R (let ([Vs*
                     (for/list : (Listof -V) ([V (in-list Vs)] [s (in-list ss)])
                       (V+ σ V (predicates-of Γ s)))])
                (apply p∋Vs σ p Vs*))
              (let ()
                (define Γ*
                  (for/fold ([Γ : -Γ Γ]) ([V (in-list Vs)] [s (in-list ss)] #:when s)
                    (match V
                      [(-● ps)
                       (for/fold ([Γ : -Γ Γ]) ([p (in-set ps)])
                         (Γ+ Γ (-?@ p s)))]
                      [(? -b? b)
                       (Γ+ Γ (-@ 'equal? (list s b) +ℓ₀))]
                      [_ Γ])))
                (MΓ⊢s M Γ* (apply -?@ p ss)))))
    (printf "~a ⊢ ~a ~a : ~a~n" (show-Γ Γ) (show-o p) (map show-W¹ Ws) R)))

(: MΓ+/-oW : -M -σ -Γ -o -W¹ * → (Values (Option -Γ) (Option -Γ)))
(define (MΓ+/-oW M σ Γ o . Ws)
  (define ss (map -W¹-s Ws))
  (Γ+/-R (apply MΓ⊢oW M σ Γ o Ws) Γ (apply -?@ o ss)))

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
      (for ([φ φs]) (printf "~a~n" (show-e φ)))
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

(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Plausibility checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: plausible-return? : -M -Γ -γ -Γ → Boolean)
(define plausible-return? ext-plausible-return?)

(: plausible-return?/cheap : -M -Γ -γ -Γ → Boolean)
(define (plausible-return?/cheap M Γₑᵣ γ Γₑₑ)
  (match-define (-Γ φs _ _) Γₑᵣ)
  (ext-plausible-return? M (-Γ φs (hasheq) '()) γ Γₑₑ))

(: plausible-index? : -M -σ -Γ -W¹ Natural → Boolean)
(define (plausible-index? M σ Γ W i)
  (case (MΓ⊢oW M σ Γ 'integer? W)
    [(✓ ?)
     (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
     (case (MΓ⊢oW M σ Γ '= W Wᵢ)
       [(✗) #f]
       [else #t])]
    [else #f]))

(: plausible-indices : -M -σ -Γ -W¹ Natural Natural → (Listof Natural))
(define (plausible-indices M σ Γ W lo hi)
  (for*/list : (Listof Natural) ([i (in-range lo hi)]
                                 #:when (exact-nonnegative-integer? i) ; hack for TR
                                 #:when (plausible-index? M σ Γ W i))
    i))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Γ+/-R : -R -Γ -s → (Values (Option -Γ) (Option -Γ)))
;; Given `s`'s satisfiability in `Γ`, strengthen `Γ` both ways. `#f` represents a bogus path condition.
(define (Γ+/-R R Γ s)
  (case R
    [(✓) (values (Γ+ Γ s) #f)]
    [(✗) (values #f       (Γ+ Γ (-?@ 'not s)))]
    [(?) (values (Γ+ Γ s) (Γ+ Γ (-?@ 'not s)))]))
