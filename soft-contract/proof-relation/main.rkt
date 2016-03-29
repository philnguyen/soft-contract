#lang typed/racket/base

(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢s MσΓ⊓ spurious? Γ+/-V Γ+/-W∋Ws Γ+/-s Γ+/-
         invert-Γ
         plausible-rt?)

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "local.rkt")

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
  (define ans (MσΓ*⊢s M σ {set (cons Γ s)}))
  #;(begin
    (printf "chk: ~a ⊢ ~a : ~a ~n" (show-Γ Γ) (show-s s) ans)
    (unless (set-empty? (-Γ-tails Γ))
      (for* ([γ (-Γ-tails Γ)]
             [τ (in-value (-γ-callee γ))])
        (printf "  ~a ↦~n" (show-τ τ))
        (for ([A (M@ M τ)])
          (printf "      ~a~n" (show-A A)))))
    (printf "~n"))
  ans)

(: MσΓ*⊢s ([-M -σ (℘ (Pairof -Γ -s))] [#:depth Natural] . ->* . -R))
;; Check if proposition is provable in all possible path conditions
(define (MσΓ*⊢s M σ ps #:depth [d 5])
  (cond
    [(<= d 0) '?]
    [else
     (define-values (✓s ✗s ?s) (partition-Γs ps))
     (define ✓-mt? (set-empty? ✓s))
     (define ✗-mt? (set-empty? ✗s))
     (define ?-mt? (set-empty? ?s))

     (define ans
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
     #;(begin ; just debugging
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
       (printf "~n"))

     ans]))

(: MσΓ⊓s : -M -σ -Γ -s → (Option -Γ))
;; More powerful version of `Γ⊓` that uses global tables
(define (MσΓ⊓s M σ Γ e)
  (if (equal? '✗ (MσΓ⊢s M σ Γ e)) #f (Γ+ Γ e)))

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

(: invert-γ : -M -Γ -γ → (℘ (Pairof -Γ (HashTable -e -e))))
;; Invert "hypothesis" `γ` in path-condition `Γ`.
;; May return multiple (refined) path-conditions due to imprecision
(define (invert-γ M Γ γ)
  (match-define (-Γ φs as γs) Γ)
  ; (assert (∋ γs γ)) Not that important as long as `invert-γ` is private
  (match-define (-γ τ sₕ bnds) γ)
  (define m₀ (bnds->subst bnds))
  
  ;; If `sₕ` was created in caller's block, its free variables and callers agree (assuming α-renaming)
  (define xs (set-add-list (fvₛ sₕ) (map (inst car Var-Name -s) bnds)))
  
  (define h∅ : (HashTable -e -e) (hash))

  (define ans
    (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) ∅]) ([A (M@ M τ)])
      (match-define (cons Γ* mₑᵣ)
        (match A
          [(-ΓW Γ₀ (-W Vs sₐ))
           (define-values (mₑₑ mₑᵣ) (mk-subst m₀ sₕ bnds sₐ))
           (cons (ensure-simple-consistency (Γ⊓ (Γ/ mₑᵣ (-Γ-minus-γ Γ γ))
                                                (Γ/ mₑₑ (Γ↓ Γ₀ xs))))
                 mₑᵣ)]
          [(-ΓE Γ₀ _)
           (cons (ensure-simple-consistency (Γ⊓ (-Γ-minus-γ Γ γ)
                                                (Γ/ m₀ (Γ↓ Γ₀ xs))))
                 h∅)]))
      (if Γ* (set-add ps (cons Γ* mₑᵣ)) ps)))
  
  #;(begin ; debugging
    (printf "Invert ~a at ~a, getting:~n" (show-Γ Γ) (show-γ γ))
    (for ([Γ ans])
      (printf "  ~a~n" (show-Γ Γ))))
  
  ans)

(: invert-Γ : -M -Γ → (℘ (Pairof -Γ (HashTable -e -e))))
;; Invert all tails in path condition, accumulating substitutions that (heuristically)
;; should also be applied to unfold goal into a more provable form.
;; This does not invert new tails added as a result of inverting existing ones.
(define (invert-Γ M Γ)
  (match-define (-Γ _ _ γs) Γ)
  (define m∅ : (HashTable -e -e) (hash))
  (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) {set (cons Γ m∅)}])
            ([γ γs])
    (for/union : (℘ (Pairof -Γ (HashTable -e -e))) ([p ps])
       (match-define (cons Γ₀ m₀) p)
       (map/set
        (λ ([p : (Pairof -Γ (HashTable -e -e))])
          (match-define (cons Γ m) p)
          (cons Γ (hash-merge m₀ m)))
        (invert-γ M Γ₀ ((γ/ m₀) γ))))))

(: invert-ps : -M (℘ (Pairof -Γ -s)) → (℘ (Pairof -Γ -s)))
(define (invert-ps M ps)
  (define ans
    (for/union : (℘ (Pairof -Γ -s)) ([p ps])
    (match-define (cons Γ s) p)
    (for/set: : (℘ (Pairof -Γ -s)) ([Γ-m (invert-Γ M Γ)])
      (match-define (cons Γ* m) Γ-m)
      (cons Γ* (and s ((e/map* m) s))))))
  #;(begin
    (printf "Invert:~n")
    (for ([p ps])
      (match-define (cons Γ s) p)
      (printf "  - ~a ⊢ ~a~n" (show-Γ Γ) (show-s s)))
    (printf "Into: ~n")
    (for ([p ans])
      (match-define (cons Γ s) p)
      (printf "  - ~a ⊢ ~a~n" (show-Γ Γ) (show-s s)))
    (printf "~n"))
  ans)

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

(: bnds->subst : (Listof (Pairof Var-Name -s)) → (HashTable -e -e))
(define (bnds->subst bnds)
  (for*/hash : (HashTable -e -e) ([bnd bnds]
                                  [s (in-value (cdr bnd))] #:when s
                                  [x (in-value (car bnd))])
    (values (-x x) s)))

(: mk-subst : (HashTable -e -e) -s (Listof (Pairof Var-Name -s)) -s
            → (Values (HashTable -e -e) (HashTable -e -e)))
;; Given caller's parameters and arguments and callee's result,
;; Create a substitution to convert callee's propositions
;; to caller's meaningful propositions.
;; Return 2 maps: first map is for callee, second for caller (for possible unfoldings)
(define (mk-subst m₀ f bnds a)
  (define-values (xs₀ args) (unzip bnds))
  (define xs (∪ (list->set xs₀) (fvₛ f)))

  ;; Caller's result as the function call
  (define fargs (apply -?@ f args))
  
  ;; Unfold caller's result to callee's result if callee's result is in terms
  ;; of only variables caller understands
  (define fargs*
    (let ([all-args? (andmap (inst values Any) args)]
          [a* (s↓ a xs)])
      (and all-args? a* ((e/map m₀) a*))))
  
  (if a
      (cond [(and fargs fargs*) ; unfold if possible
             (values (hash-set m₀ a fargs*) (hash fargs fargs*))]
            [fargs
             (values (hash-set m₀ a fargs ) (hash))]
            [else
             (values m₀ (hash))])
      (values m₀ (hash))))


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
