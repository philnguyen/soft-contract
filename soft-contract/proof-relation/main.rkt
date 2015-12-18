#lang typed/racket/base

(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢e MσΓ⊓ spurious? Γ+/-W Γ+/-W∋Ws Γ+/-e Γ+/-)

(require
 racket/match racket/set racket/bool racket/function
 "../utils/set.rkt" "../utils/debug.rkt" "../utils/pretty.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/val.rkt" "../runtime/simp.rkt" "../runtime/path-inv.rkt" "../runtime/summ.rkt" "../runtime/store.rkt"
 "result.rkt" "local.rkt" "utils.rkt")

;; External solver to be plugged in.
;; Return trivial answer by default.
(define Γ⊢ₑₓₜ : (Parameterof (-M -σ -Γ -e → -R))
  (make-parameter (λ (M σ Γ e) (printf "Warning: external solver not set") '?)))

(: MσΓ⊢V∈C : -M -σ -Γ -WV -WV → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (first-R (V∋Vs C V) (MσΓ⊢e M σ Γ (-?@ e_c e_v))))

(: MσΓ⊢oW : -M -σ -Γ -o -WV * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p . Ws)
  (define-values (Vs es)
    (for/lists ([Vs : (Listof -V)] [e : (Listof -?e)])
               ([W Ws])
      (values (-W-x W) (-W-e W))))
  (first-R (apply p∋Vs p Vs)
           (MσΓ⊢e M σ Γ (apply -?@ p es))))

(: MσΓ⊢e : -M -σ -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢e M σ Γ e)
  (cond
    [e
     (define e* (canonicalize Γ e))
     (first-R (MσΓ⊢₁e M σ Γ e*) ((Γ⊢ₑₓₜ) M σ Γ e*))]
    [else '?]))

(: MσΓ⊢₁e : -M -σ -Γ -e → -R)
;; Check if `e` evals to truth given `M`, `σ`, `Γ`
(define (MσΓ⊢₁e M σ Γ e)
  (define FVe (FV e))

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
               [(equal? Rs {set 'X }) 'X ]
               [else '?])])])]
      [R R]))

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
                 (for*/set: : (Setof -R)
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
                 [(equal? anses {set 'X}) 'X]
                 [else '?])]
              [else '?])])]
        [R R]))
    (dbg '⊢rec "~a ⊢~a ~a : ~a~n" (show-Γ Γ) (n-sub d) (show-e e) ans)
    ans)

  (dbg '⊢rec "~n")
  (first-R (go 2 Γ) (go-rec 2 Γ e)))

(: MσΓ⊓e : -M -σ -Γ -?e → (Option -Γ))
;; More powerful version of `Γ⊓` that uses global tables
(define (MσΓ⊓e M σ Γ e)
  (if (equal? 'X (MσΓ⊢e M σ Γ e)) #f (Γ+ Γ e)))

(: MσΓ⊓ : -M -σ -Γ -es → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (MσΓ⊓ M σ Γ es)
  (for/fold ([Γ : (Option -Γ) Γ]) ([e es])
    (and Γ (MσΓ⊓e M σ Γ e))))

(: spurious? : -M -σ -Γ -WVs → Boolean)
;; Check if `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (conservative answer)
(define (spurious? M σ Γ W)

  (: spurious*? : -?e -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(or (-St s _) (-St/checked s _ _ _))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ (-st-p (assert s)) e)))]
           [(or (? -Vector?) (? -Vector/checked?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'vector? e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'p? e)))] ...
           [(or (? -=>i?) (? -St/C?) (? -x/C?))
            (for/or : Boolean ([p : -o '(procedure? p? ...)])
              (equal? '✓ (MσΓ⊢e M σ Γ (-?@ p e))))]
           ['undefined
            (match e
              [(-x x) (Γ-binds? Γ x)]
              [_ #f])]
           [(-●)
            (match e
              [(-not e*) (equal? '✓ (MσΓ⊢e M σ Γ e*))]
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

(: Γ+/-W : -M -σ -Γ -WV → (Values (Option -Γ) (Option -Γ)))
;; Like `(Γ ⊓ W)` and `(Γ ⊓ ¬W)`, probably faster
(define (Γ+/-W M σ Γ W)
  (match-define (-W V e) W)
  (define proved (first-R (⊢V V) (MσΓ⊢e M σ Γ e)))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))

(: Γ+/-W∋Ws : -M -σ -Γ -WV -WV * → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `P(V…)` and `¬P(V…)`
(define (Γ+/-W∋Ws M σ Γ W_P . W_Vs)
  (match-define (-W P e_p) W_P)
  (define-values (Vs e_vs)
    (for/lists ([Vs : (Listof -V)] [e_vs : (Listof -?e)])
               ([W W_Vs])
      (values (-W-x W) (-W-e W))))
  (define ψ (apply -?@ e_p e_vs))
  (define proved (first-R (apply V∋Vs P Vs) (MσΓ⊢e M σ Γ ψ)))
  (values (if (equal? 'X proved) #f (Γ+ Γ ψ))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not ψ)))))

(: Γ+/-e : -M -σ -Γ -?e → (Values (Option -Γ) (Option -Γ)))
(define (Γ+/-e M σ Γ e)
  (define proved (MσΓ⊢e M σ Γ e))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))

(: Γ+/- (∀ (X Y) -M -σ -Γ (-Γ → X)
           (U (List -WV (Listof -WV) (-Γ → Y))
              (List 'not -WV (Listof -WV) (-Γ → Y))) *
           → (Values (Option X) (Setof Y))))
;; Refine the environment with sequence of propositions
;; and return (maybe) final sucessful environment
;; along with each possible failure
;; e.g. {} +/- ([num? n₁] [num? n₂]) -->
;;      (values {num? n₁, num? n₂} {{¬ num? n₁}, {num? n₁, ¬ num? n₂}})
(define (Γ+/- M σ Γ mk-ok . filters)
  (define-values (Γ-ok ans-bads)
    (for/fold ([Γ-ok : (Option -Γ) Γ]
               [ans-bads : (Setof Y) ∅])
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

(: Γ+/-AΓ : -M -σ -Γ (-Γ → -AΓ)
            (U (List -WV (Listof -WV) (-Γ → -AΓ))
            (List 'not -WV (Listof -WV) (-Γ → -AΓ))) * → -AΓs)
(define (Γ+/-AΓ M σ Γ mk-ok . filters)
  (define-values (ans-ok ans-bads) (apply Γ+/- M σ Γ mk-ok filters))
  (cond [ans-ok (cond [(set-empty? ans-bads) ans-ok]
                      [else (set-add ans-bads ans-ok)])]
        [else ans-bads]))

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
      (⊔ -σ⊥ (-α.def (-id 'app '†)) (-Clo '(l₁ l₂) -app-body -ρ⊥ -Γ⊤))
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

  (check-equal? (MσΓ⊢e Mdb σdb -Γ⊤ e-len-app) '✓)
  (check-equal? (MσΓ⊢e Mdb σdb -Γ⊤ e-len-map) '✓))
