#lang typed/racket/base

(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢s MσΓ⊓ spurious? Γ+/-V Γ+/-W∋Ws Γ+/-s Γ+/-)

(require
 racket/match racket/set racket/bool (except-in racket/function arity-includes?)
 "../utils/main.rkt" "../ast/main.rkt"
 "../runtime/main.rkt"
 "result.rkt" "local.rkt" "utils.rkt")

;; External solver to be plugged in.
;; Return trivial answer by default.
(define-parameter Γ⊢ₑₓₜ : (-M -σ -Γ -e → -R)
  (λ (M σ Γ e)
    (printf "Warning: external solver not set~n")
    '?))

(: MσΓ⊢V∈C : -M -σ -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (MσΓ⊢s M σ Γ (-?@ e_c e_v)))

(: MσΓ⊢oW : -M -σ -Γ -o -W¹ * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (first-R (apply p∋Vs p Vs)
           (MσΓ⊢s M σ Γ (apply -?@ p ss))))

(: MσΓ⊢s : -M -σ -Γ -s → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢s M σ Γ s)
  ;; TODO make sure `s` has been canonicalized
  (if s (first-R (MσΓ⊢₁e M σ Γ s) ((Γ⊢ₑₓₜ) M σ Γ s)) '?))

(: MσΓ⊢₁e : -M -σ -Γ -e → -R)
;; Check if `e` evals to truth given `M`, `σ`, `Γ`
(define (MσΓ⊢₁e M σ Γ e)

  #|
  (: go : Integer -Γ → -R)
  ;; Try proving goal by probably repeatedly unfolding assumptions
  (define (go d Γ)
    (match (Γ⊢e Γ e)
      ['?
       (cond
         [(< d 0) '?]
         [else
          (define Γs (invert-Γ M σ (Γ↓ Γ FVe)))
          (cond ; if one subcase repeats, there can't be progress
            [(∋ Γs Γ) '?]
            [else
             (define Rs (map/set (curry go (- d 1)) Γs))
             (cond
               [(equal? Rs {set '✓}) '✓]
               [(equal? Rs {set '✗ }) '✗ ]
               [else '?])])])]
      [R R]))
  |#

  #|
  (: go-rec : Integer -Γ -e → -R)
  ;; Try proving goal probably by rule induction
  (define (go-rec d Γ e)
    (define ans
      (match (Γ⊢e Γ e) ; FIXME: shift things around. This is wasteful.
        ['?
         (cond
           [(< d 0) '?]
           [else
            (match (unfold M σ e)
              [(? set? cases)
               (define anses
                 (for*/set: : (℘ -R)
                            ([kase cases]
                             [ψs (in-value (-Res-facts kase))]
                             [e* (in-value (-Res-e     kase))]
                             [Γ* (in-value (Γ⊓ Γ ψs))] #:when Γ*)
                   (cond
                     [e*
                      (define-values (e** Γ**) (⇓₁ M σ Γ* (assert e*)))
                      (go-rec (- d 1) Γ** e**)]
                     [else '?])))
               (cond
                 [(or (set-empty? anses) (equal? anses {set '✓})) '✓]
                 [(equal? anses {set '✗}) '✗]
                 [else '?])]
              [else '?])])]
        [R R]))
    (dbg '⊢rec "~a ⊢~a ~a : ~a~n" (show-Γ Γ) (n-sub d) (show-e e) ans)
    ans)
  |#

  ;(first-R (go 2 Γ) (go-rec 2 Γ e))
  (Γ⊢e Γ e))

(: MσΓ⊓s : -M -σ -Γ -s → (Option -Γ))
;; More powerful version of `Γ⊓` that uses global tables
(define (MσΓ⊓s M σ Γ e)
  (if (equal? '✗ (MσΓ⊢s M σ Γ e)) #f (Γ+ Γ e)))

(: MσΓ⊓ : -M -σ -Γ -es → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (MσΓ⊓ M σ Γ es)
  (for/fold ([Γ : (Option -Γ) Γ]) ([e es])
    (and Γ (MσΓ⊓s M σ Γ e))))

(: spurious? : -M -σ -Γ -W → Boolean)
;; Check if `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (conservative answer)
(define (spurious? M σ Γ W)

  (: spurious*? : -s -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(or (-St s _) (-St/checked s _ _ _))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ (-st-p (assert s)) e)))]
           [(or (? -Vector?) (? -Vector/checked?) (? -Vector/same?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'vector? e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'p? e)))] ...
           [(or (? -=>i?) (? -St/C?) (? -x/C?))
            (for/or : Boolean ([p : -o '(procedure? p? ...)])
              (equal? '✓ (MσΓ⊢s M σ Γ (-?@ p e))))]
           ['undefined (equal? '✓ (Γ⊢e Γ (-?@ 'defined? e)))]
           [(-●)
            (match e
              [(-not e*) (equal? '✓ (MσΓ⊢s M σ Γ e*))]
              [_ #f])]
           [_ #f])]
        [else #f]))
    
    ;; order matters for precision, in the presence of subtypes
    (with-prim-checks integer? real? number? string? symbol? keyword? not boolean?))
  
  (match-define (-W Vs e) W)
  (match e
    [(-@ 'values es _)
     (implies (= (length es) (length Vs))
              (ormap spurious*? es Vs))]
    [_
     (match Vs
       [(list V) (spurious*? e V)]
       [_ #f])]))

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
  (Γ+/-R (MσΓ⊢s M σ Γ ψ) Γ ψ))

(: Γ+/-s : -M -σ -Γ -s → (Values (Option -Γ) (Option -Γ)))
(define (Γ+/-s M σ Γ s)
  (Γ+/-R (MσΓ⊢s M σ Γ s) Γ s))

(: Γ+/- (∀ (X Y) -M -σ -Γ (-Γ → X)
           (U (List -W¹ (Listof -W¹) (-Γ → Y))
              (List 'not -W¹ (Listof -W¹) (-Γ → Y))) *
           → (Values (Option X) (℘ Y))))
;; Refine the environment with sequence of propositions
;; and return (maybe) final sucessful environment
;; along with each possible failure
;; e.g. {} +/- ([num? n₁] [num? n₂]) -->
;;      (values {num? n₁, num? n₂} {{¬ num? n₁}, {num? n₁, ¬ num? n₂}})
(define (Γ+/- M σ Γ mk-ok . filters)
  (define-values (Γ-ok ans-bads)
    (for/fold ([Γ-ok : (Option -Γ) Γ]
               [ans-bads : (℘ Y) ∅])
              ([filt filters])
      (cond
        [Γ-ok
         (define-values (Γ-ok* Γ-bad* mk-bad)
           (match filt
             [(list W-p W-vs mk-bad)
              (define-values (Γ-sat Γ-unsat) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
              (values Γ-sat Γ-unsat mk-bad)]
             [(list 'not W-p W-vs mk-bad)
              (define-values (Γ-sat Γ-unsat) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
              (values Γ-unsat Γ-sat mk-bad)]))
         (define ans-bads*
           (cond [Γ-bad* (set-add ans-bads (mk-bad Γ-bad*))]
                 [else ans-bads]))
         (values Γ-ok* ans-bads*)]
        [else (values #f ans-bads)])))
  (values (and Γ-ok (mk-ok Γ-ok)) ans-bads))

(: Γ+/-AΓ : -M -σ -Γ (-Γ → -A)
            (U (List -W¹ (Listof -W¹) (-Γ → -A))
            (List 'not -W¹ (Listof -W¹) (-Γ → -A))) * → (U -A (℘ -A)))
(define (Γ+/-AΓ M σ Γ mk-ok . filters)
  (define-values (ans-ok ans-bads) (apply Γ+/- M σ Γ mk-ok filters))
  (cond [ans-ok (cond [(set-empty? ans-bads) ans-ok]
                      [else (set-add ans-bads ans-ok)])]
        [else ans-bads]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Γ+/-R : -R -Γ -s → (Values (Option -Γ) (Option -Γ)))
;; Given `s`'s satisfiability in `Γ`, strengthen `Γ` both ways. `#f` represents a bogus path condition.
(define (Γ+/-R R Γ s)
  (case R
    [(✓)  (values (Γ+ Γ s) #f)]
    [(✗)  (values #f       (Γ+ Γ (-not s)))]
    [else (values (Γ+ Γ s) (Γ+ Γ (-not s)))]))

#|
(module+ test
  (require typed/rackunit "../utils/map.rkt" "../runtime/addr.rkt" "../runtime/env.rkt" "for-test.rkt")

  (define -app (-ref (-id 'app '†) '† 0))
  (define -app-body (-b 'app-body))
  (define -len (-ref (-id 'len '†) '† 0))
  (define -len-body (-b 'len-body))
  (define -map (-ref (-id 'map '†) '† 0))
  (define -map-body (-b 'map-body))
  (define -l₁ (-x 'l₁))
  (define -l₂ (-x 'l₂))
  (define -xs (-x 'xs))
  (define -ys (-x 'ys))
  (define -f (-x 'f))
  (define e-len-app
    (assert (-?@ 'equal?
                 (-?@ -len (-?@ -app -xs -ys))
                 (-?@ '+ (-?@ -len -xs) (-?@ -len -ys)))))
  (define e-len-map
    (assert (-?@ 'equal?
                 (-?@ -len (-?@ -map -f -xs))
                 (-?@ -len -xs))))
  ;(define Γdb : -Γ {set edb})
  (define σdb
    (⊔
     (⊔
      (⊔ ⊥σ (-α.def (-id 'app '†)) (-Clo '(l₁ l₂) -app-body -ρ⊥))
      (-α.def (-id 'len '†)) (-Clo '(l) -len-body -ρ⊥ -Γ⊤))
     (-α.def (-id 'map '†)) (-Clo '(f xs) -map-body -ρ⊥ -Γ⊤)))
  (define Mdb
    (⊔
     (⊔
      (⊔
       (⊔
        (⊔
         (⊔ -M⊥ -app-body (-Res -l₂ {set (assert (-?@ 'null? -l₁))}))
         -app-body
         (-Res
          (-?@ -cons (-?@ -car -l₁) (-?@ -app (-?@ -cdr -l₁) -l₂))
          {set (assert (-?@ -cons? -l₁))}))
        -len-body
        (-Res (-b 0) {set (assert (-?@ 'null? (-x 'l)))}))
       -len-body
       (-Res (-?@ '+ (-b 1) (-?@ -len (-?@ -cdr (-x 'l))))
             {set (assert (-?@ -cons? (-x 'l)))}))
      -map-body
      (-Res -null {set (assert (-?@ 'null? -xs))}))
     -map-body
     (-Res (-?@ -cons (-?@ -f (-?@ -car -xs)) (-?@ -map -f (-?@ -cdr -xs)))
           {set (assert (-?@ -cons? -xs))})))

  (check-equal? (MσΓ⊢s Mdb σdb -Γ⊤ e-len-app) '✓)
  (check-equal? (MσΓ⊢s Mdb σdb -Γ⊤ e-len-map) '✓))
|#
