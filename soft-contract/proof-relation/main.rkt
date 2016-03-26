#lang typed/racket/base

(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢s MσΓ⊓ spurious? Γ+/-V Γ+/-W∋Ws Γ+/-s Γ+/-
         invert-γ invert-Γ)

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "local.rkt"
         "utils.rkt")

(: MσΓ⊢V∈C : -M -σ -Γ -W¹ -W¹ → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W¹ V e_v) W_v)
  (match-define (-W¹ C e_c) W_c)
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
  (MσΓ*⊢s M σ {set Γ} s))

(: MσΓ*⊢s ([-M -σ (℘ -Γ) -s] [#:depth Natural] . ->* . -R))
;; Check if proposition is provable in all possible path conditions
(define (MσΓ*⊢s M σ Γs s #:depth [d 5])
  (cond
    [(or (not s) (<= d 0)) '?]
    [else
     (define-values (✓Γ ✗Γ ?Γ) (partition-Γs Γs s))

     (begin ; just debugging
       (printf "worlds:~n")
       (for ([Γ Γs])
         (printf "  ~a ⊢ ~a : ~a~n"
                 (show-Γ Γ)
                 (show-s s)
                 (cond [(∋ ✓Γ Γ) '✓]
                       [(∋ ✗Γ Γ) '✗]
                       [(∋ ?Γ Γ) '?]
                       [else (error 'MσΓ*⊢s "wrong")]))))
     
     (match* ((set-empty? ✓Γ) (set-empty? ✗Γ) (set-empty? ?Γ))
       [(#f #f _ ) '?]
       [(_  #t #t) '✓]
       [(#t #f #t) '✗]
       [(_  _  #f) (MσΓ*⊢s M σ ?Γ s #:depth (- d 1))])]))

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
           [(or (-St s _) (-St* s _ _ _))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ (-st-p (assert s)) e)))]
           [(or (? -Vector?) (? -Vector/hetero?) (? -Vector/homo?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'vector? e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? '✗ (MσΓ⊢s M σ Γ (-?@ 'p? e)))] ...
           [(or (? -=>_?) (? -St/C?) (? -x/C?))
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
  (define R (first-R (apply p∋Vs P Vs) (MσΓ⊢s M σ Γ ψ)))
  (Γ+/-R R Γ ψ))

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
;;;;; Inversion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: invert-γ : -M -Γ -γ → (℘ -Γ))
;; Invert "hypothesis" `γ` in path-condition `Γ`.
;; May return multiple (refined) path-conditions due to imprecision
(define (invert-γ M Γ γ)
  (match-define (-Γ φs as γs) Γ)
  (assert (∋ γs γ))

  (match-define (-γ τ sₕ x→as) γ)
  (define-values (m₀ xs)
    (for/fold ([m : (HashTable -e -e) (hash)]
               [xs : (℘ Var-Name) ∅])
              ([x→a (in-list x→as)])
      (match-define (cons x sₓ) x→a)
      (values (if sₓ (hash-set m (-x x) sₓ) m)
              (set-add xs x))))

  (define-values (sₓ sₑ) (unzip x→as))
  (define sₕₑ (apply -?@ sₕ sₑ))
  (define all-args? (andmap (compose1 not not) sₑ))

  (for/fold ([Γs : (℘ -Γ) ∅]) ([A (M@ M τ)])
    (define Γ*
      (match A
        [(-ΓW Γ₀ (-W Vs sₐ))
         ;; When returning callee's `eₐ` to caller's `f eₓ ...":
         ;; - unfold eₐ to [x/eₓ]eₐ if possible
         ;; - if not, replace `eₐ` with `f eₓ ...`
         (define sₐ* (s↓ sₐ xs))
         (define sₕₑ* (and all-args? sₐ* ((e/map m₀) sₐ*)))
         (define m
           (if sₐ*
               (cond [sₕₑ* (hash-set m₀ sₐ* sₕₑ*)]
                     [sₕₑ  (hash-set m₀ sₐ* sₕₑ )]
                     [else m₀])
               m₀))
         (Γ⊓ Γ (Γ/ m (Γ↓ Γ₀ xs)))]
        [(-ΓE Γ₀ _)
         (Γ⊓ Γ (Γ/ m₀ (Γ↓ Γ₀ xs)))]))
    (match Γ* ; Throw away the inverted hypothesis
      [(-Γ φs as γs)
       (set-add Γs (-Γ φs as (set-remove γs γ)))]
      [#f Γs])))

(: invert-Γ : -M -Γ → (℘ -Γ))
;; Invert all tails in path condition
(define (invert-Γ M Γ)
  (match-define (-Γ _ _ γs) Γ)
  (for/fold ([Γs : (℘ -Γ) {set Γ}])
            ([γ γs])
    (for/union : (℘ -Γ) ([Γ Γs])
       (invert-γ M Γ γ))))

(: invertⁿ-Γ : Natural -M -Γ → (℘ -Γ))
;; Invert all tails in path condition `n` times
(define (invertⁿ-Γ n M Γ)
  (for/fold ([Γs : (℘ -Γ) {set Γ}]) ([_ n])
    (for/union : (℘ -Γ) ([Γ Γs])
       (invert-Γ M Γ))))

(: Γ⊓ : -Γ -Γ → (Option -Γ))
;; Less powerful version of `Γ` that only proves things using local assumptions
(define (Γ⊓ Γ₀ Γ₁)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (define Γ₀*
    (for/fold ([Γ₀ : (Option -Γ) Γ₀]) ([φ₁ φs₁])
      (and Γ₀
           (case (Γ⊢e Γ₀ φ₁)
             [(✓ ?) (Γ+ Γ₀ φ₁)]
             [(✗)   #f]))))
  (match Γ₀*
    [(-Γ φs₀ as₀ γs₀) (-Γ φs₀ as₀ (∪ γs₀ γs₁))]
    [#f #f]))


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
