#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "utils.rkt" "ast.rkt" "runtime.rkt")
(provide MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢e V∈p V≡
         MσΓ⊓ Γ+/-W Γ+/-W∈W spurious? or-R not-R decide-R
         -R
         ;; debugging
         MσΓ⊢₁e Γ⊢e)

(define Γ⊢ₑₓₜ : (Parameterof (-M -σ -Γ -e → -R))
  (make-parameter (λ (M σ Γ e) (log-warning "external solver not set") '?)))

(: MσΓ⊢V∈C : -M -σ -Γ -WV -WV → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (or-R (V∈V V C) (MσΓ⊢e M σ Γ (-?@ e_c e_v))))

(: MσΓ⊢oW : -M -σ -Γ -pred -WV → -R)
;; Check if value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p W)
  (match-define (-W V e) W)
  (or-R (V∈p V p) (MσΓ⊢e M σ Γ (-?@ p e))))

(: MσΓ⊢e : -M -σ -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢e M σ Γ e)
  (cond
    [e
     (define e* (canonicalize Γ e))
     (or-R (MσΓ⊢₁e M σ Γ e*) ((Γ⊢ₑₓₜ) M σ Γ e*))]
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
             (define Rs
               (for/set: : (Setof -R) ([Γi Γs])
                 (go (- d 1) Γi)))
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
                   (define-values (e** Γ**) (⇓₁ M σ Γ* (assert e*)))
                   (go-rec (- d 1) Γ** e**)))
               (cond
                 [(or (set-empty? anses) (equal? anses {set '✓})) '✓]
                 [(equal? anses {set 'X}) 'X]
                 [else '?])]
              [else '?])])]
        [R R]))
    (dbg '⊢rec "~a ⊢~a ~a : ~a~n" (show-Γ Γ) (n-sub d) (show-e e) ans)
    ans)

  (dbg '⊢rec "~n")
  (or-R (go 2 Γ) (go-rec 2 Γ e)))

(: MσΓ⊓e : -M -σ -Γ -?e → (Option -Γ))
;; More powerful version of `Γ⊓`
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
;;   return #f --> don't know (safe answer)
(define (spurious? M σ Γ W)

  (: spurious*? : -?e -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(or (-St s _) (-St/checked s _ _ _))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ (-st-p (assert s)) e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'p? e)))] ...
           [(or (? -=>i?) (? -St/C?) (? -μ/C?) (? -X/C?))
            (for/or : Boolean ([p : -o '(procedure? p? ...)])
              (equal? '✓ (MσΓ⊢e M σ Γ (-?@ p e))))]
           ['undefined
            (match e
              [(-x x) (Γ-binds? Γ x)]
              [_ #f])]
           ['•
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
  (define proved (or-R (⊢V V) (MσΓ⊢e M σ Γ e)))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))

(: Γ+/-W∈W : -M -σ -Γ -WV -WV → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `V∈P` and `V∉P`
(define (Γ+/-W∈W M σ Γ W_V W_P)
  (match-define (-W V e_v) W_V)
  (match-define (-W P e_p) W_P)
  (define ψ (-?@ e_p e_v))
  (define proved (or-R (V∈V V P) (MσΓ⊢e M σ Γ ψ)))
  (values (if (equal? 'X proved) #f (Γ+ Γ ψ))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not ψ)))))

(: Γ+/-e : -M -σ -Γ -?e → (Values (Option -Γ) (Option -Γ)))
(define (Γ+/-e M σ Γ e)
  (define proved (MσΓ⊢e M σ Γ e))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Operations without global tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Γ⊢e : -Γ -?e → -R)
;; Check if `e` evals to truth given `M`
(define (Γ⊢e Γ e)

  (: ⊢e : -e → -R)
  ;; Check if expression returns truth
  (define (⊢e e)
    (define ans
      (match e
        ;; values
        [(-b #f) 'X]
        [(? -•?) '?]
        [(? -v?) '✓]
        [(? (curry Γ-has? Γ)) '✓]
        ;; constructors
        [(or (? -μ/c?) (? -->i?) (? -x/c?) (? -struct/c?)) '✓]
        ;; special cases
        [(-@ (or '= 'equal?) (list e₁ e₂) _)
         (match* (e₁ e₂)
           [((? -λ? v₁) (? -λ? v₂)) ; can't compare higher-order literals
            (if (equal? v₁ v₂) '? 'X)]
           [((? -•?) _) '?]
           [(_ (? -•?)) '?]
           [((? -v? v₁) (? -v? v₂)) (decide-R (equal? v₁ v₂))]
           [((-x x) (-x y))
            (if (equal? x y) '✓ '?)]
           [((-@ f xs _) (-@ g ys _))
            ; lose precision. Don't need `f = g, x = y` to prove `f(x) = g(y)`
            (cond
              [(and
                (or
                 (and (-λ? f) (equal? f g))
                 (equal? '✓ (⊢e (-@ 'equal? (list f g) -Λ))))
                (= (length xs) (length ys)))
               (define res
                 (for/set: : (Setof -R) ([x xs] [y ys])
                   (⊢e (-@ 'equal? (list x y) -Λ))))
               (cond
                 [(or (set-empty? res) (equal? res {set '✓})) '✓]
                 [(and (-st-mk? f) (∋ res 'X)) 'X]
                 [else '?])]
              [else '?])]
           [(_ _) (if (equal? e₁ e₂) '✓ '?)])]
        ;; negation
        [(-not e*) (not-R (⊢e e*))]
        ;; ariths
        [(-@ 'integer? (list e*) _)
         (match e*
           [(-b b) (decide-R (real? b))]
           [(-@ o (list es ...) _)
            (match o
              [(or 'string-length 'vector-length #|TODO|# 'round 'floor 'ceiling) '✓]
              [(or '+ '- '* 'add1 'sub1 'abs)
               (cond [(for/and : Boolean ([ei es])
                        (equal? '✓ (Γ⊢e Γ (assert (-?@ 'integer? ei)))))
                      '✓]
                     [else '?])]
              [(or (? -pred?) (? -st-mk?)) 'X]
              [_ '?])]
           [_ '?])]
        [(-@ 'real? (list e*) _)
         (match e*
           [(-b b) (decide-R (real? b))]
           [(-@ o (list es ...) _)
            (match o
              [(or 'string-length 'vector-length 'round 'floor 'ceiling) '✓]
              [(or '+ '- '* 'add1 'sub1 'abs)
               (cond [(for/and : Boolean ([ei es])
                        (equal? '✓ (Γ⊢e Γ (assert (-?@ 'real? ei)))))
                      '✓]
                     [else '?])]
              [(or (? -pred?) (? -st-mk?)) 'X]
              [_ '?])]
           [_ '?])]
        [(-@ 'number? (list e*) _)
         (match e*
           [(-b b) (decide-R (number? b))]
           [(-@ o (list es ...) _)
            (match o
              [(or 'string-length 'vector-length 'round 'floor 'ceiling
                   '+ '- '* 'add1 'sub1 'abs)
               '✓]
              [(or (? -pred?) (? -st-mk?)) 'X]
              [_ '?])]
           [_ '?])]
        [(-@ 'boolean? (list e*) _)
         (match e*
           [(-b b) (decide-R (boolean? b))]
           [(-@ (? -pred?) _ _) '✓]
           [(-@ 'equal? _ _) '✓]
           [(-@ (? -st-mk?) _ _) 'X]
           [_ '?])]
        [(-@ (-st-p s) (list e*) _)
         (match e*
           [(-@ (-st-mk s*) _ _)
            (decide-R (equal? s s*))]
           [(or (? -b?) (? -λ?)) 'X]
           [_ '?])]
        [(-@ (? -st-ac?) (list e) _) '?]
        [(-@ (? -o?) _ _) '✓] ; happens to be so for now
        [_ '?]))
    (dbg '⊢e "⊢ ~a : ~a~n~n" (show-e e) ans)
    ans)

  (: e⊢e : -e -e → -R)
  ;; Check if `e₂` returns truth when `e₁` does
  (define (e⊢e e₁ e₂)
    (define ans
      (match* ((⊢e e₁) (⊢e e₂))
        [('X _) '✓]
        [(_ '?)
         (match* (e₁ e₂)
           ; e ⇒ e
           [(e e) '✓]
           ; NOTE: Don't abuse "contrapositive"
           ; (¬e₁ ⊢ ¬e₂ : X) does not follow from (e₂ ⊢ e₁ : X)
           [((-not e₁*) (-not e₂*))
            (if (equal? '✓ (e⊢e e₂* e₁*)) '✓ '?)]
           [(e₁ (-not e₂*))
            (not-R (e⊢e e₁ e₂*))]
           [((-@ (? -pred? p) (list e) _) (-@ (? -pred? q) (list e) _))
            (p⇒p p q)]
           [((-@ (? -pred? p) (list e) _) e)
            (cond
              [(equal? p 'not) 'X]
              [(equal? p 'boolean?) '?]
              [else '✓])]
           [(_ _) '?])]
        [(_ R) R]))
    (dbg 'e⊢e "~a ⊢ ~a : ~a~n~n" (show-e e₁) (show-e e₂) ans)
    ans)
  
  (define ans
    (cond
      [e
       (or-R (⊢e e)
             (for*/fold ([R : -R '?])
                        ([e₀ (-Γ-facts Γ)] #:when (equal? '? R)
                         [R* (in-value (e⊢e e₀ e))])
               R*))]
      [else '?]))
  (dbg '⊢ "~a ⊢ ~a : ~a~n~n"(show-Γ Γ) (show-?e e) ans)
  ans)

(: ⊢V : -V → -R)
;; Check if value represents truth
(define ⊢V
  (match-lambda
    [(-b #f) 'X]
    ['• '?]
    [_ '✓]))

(: V∈V : -V -V → -R)
;; Check if value satisfies predicate
(define (V∈V V P)
  (cond
    [(-pred? P) (V∈p V P)]
    [else
     (match P
       [(-Clo `(,x) (-b #f) _ _) 'X]
       [(-Clo `(,x) (? -v? v) _ _) (if (-•? v) '? '✓)]
       [(-Clo `(,x) (-x x) _ _) (⊢V V)]
       [_ '?])]))

(: V∈p : -V -pred → -R)
;; Check if value satisfies predicate
(define (V∈p V p)
  (define-syntax-rule (with-prim-checks p? ...)
    (case p
      [(p?)
       (match V
         [(-b (? p?)) '✓]
         ['• '?]
         [_ 'X])] ...
      [(procedure?)
       (match V
         [(or (? -o?) (? -Clo?) (? -Clo*?) (? -Ar?)) '✓]
         ['• '?]
         [_ 'X])]
      [(vector?)
       (match V
         [(? -Vector?) '✓]
         ['• '?]
         [_ 'X])]
      [else
       (match-define (-st-p s) p)
       (match V
         [(or (-St s* _) (-St/checked s* _ _ _))
          (decide-R (equal? s (assert s*)))]
         ['• '?]
         [_ 'X])]))
  (with-prim-checks integer? real? number? not boolean? string? symbol? keyword?))

(: V≡ : -V -V → -R)
;; Check if 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (decide-R (equal? x₁ x₂))]
   [(_ _) '?]))

(: p⇒p : -pred -pred → -R)
(define (p⇒p p q)
  (cond
    [(equal? p q) '✓]
    [else ; when p ≠ q
     (match* (p q)
       ; boolean
       [('not 'boolean?) '✓]
       [('boolean? 'not) '?]
       ; number
       [('integer? (or 'real? 'number?)) '✓]
       [('real? 'number?) '✓]
       [('number? (or 'real? 'integer?)) '?]
       [('real? 'integer?) '?]
       ; other cases, `p` known to exclude `q` (be careful)
       [(_ _) 'X])]))

(: Γ⊓ : -Γ -es → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (Γ⊓ Γ es)
  (for/fold ([Γ : (Option -Γ) Γ]) ([e es])
    (and Γ (Γ⊓e Γ e))))

(: Γ⊓e : -Γ -?e → (Option -Γ))
;; Refine path invariant with expression.
;; Note: `∅` is `⊤` (no assumption), `#f` is `⊥` (spurious, anything is true).
;; The operation doesn't guarantee absolute precision.
;; In general, it returns an upperbound of the right answer.
(define (Γ⊓e Γ e)
  (if (equal? 'X (Γ⊢e Γ e)) #f (Γ+ Γ e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: invert-e : -M -σ -id (Listof -e) → (Setof -Res))
;; Given proposition `(p? v)`, generate an overapproximation of expressions
;; that could have evaluated to it
(define (invert-e M σ f args)

  (define α (-α.def f))
  (match/nd: (-V → -Res) (σ@ σ α)
    [(or (-Clo (? list? xs) e _ _) (-Clo* (? list? xs) e _))
     ;; Convert invariant about parameters into one about arguments
     (define (convert [e : -e]) : -e
       (for/fold ([e : -e e]) ([x (assert xs)] [arg args])
         (e/ e x arg)))
     
     (match/nd: (-Res → -Res) (hash-ref M (assert e))
       [(-Res e-xs ψ-xs)
        (define e-args (and e-xs (convert e-xs)))
        (define ψ-args (for/set: : -es ([ψ ψ-xs]) (convert ψ)))
        (-Res e-args ψ-args)])]
        
    [_ -Res⊤]))

(: invert-Γ : -M -σ -Γ → (Setof -Γ))
;; Given propositions `Γ`, generate an overapproximation of environments
;; that could have derived it
(define (invert-Γ M σ Γ)
  (match-define (-Γ bnds facts) Γ)

  ; split environment into propositions that can be further unrolled and the rest
  (define-values (ψs-unrollable ψs₀)
    (set-partition (match-λ? (-@ (? -ref?) _ _)) facts))

  (: go : (Setof -Γ) (Listof -e) → (Setof -Γ))
  ; Join each base environment in `Γs` with each possible inversion of `φs`
  (define (go Γs φs)
    (match φs
      ['() Γs]
      [(cons φ φs*)
       (match-define (-@ (-ref id _ _) xs _) φ)
       (for*/fold ([acc : (Setof -Γ) ∅])
                  ([kase : -Res (invert-e M σ id xs)]
                   [Γ : -Γ (go Γs φs*)])
         (match-define (-Res ψ_i ψs_i) kase)
         (define Γ₁ (if ψ_i (Γ⊓e Γ ψ_i) Γ))
         (define Γ₂ (and Γ₁ (Γ⊓ Γ₁ ψs_i)))
         (if Γ₂ (set-add acc Γ₂) acc))]))

  (go (set (-Γ bnds ψs₀)) (set->list ψs-unrollable)))

(: unfold ([-M -σ -e] [(-id (Listof -e) → Boolean)] . ->* . (Option (Setof -Res))))
;; Unfold the first appropriate expression according to `unfold-this-one?`.
;; Return #f if couldn't find one to unfold.
(define (unfold M σ e₀ [unfold-this-one? (λ (id args) #t)])

  (: go : -e → (Option (Setof -Res)))
  (define (go e)
    (match e
      [(-@ f xs l)
       (match (go* (cons f xs))
         [#f
          (match f
            [(-ref id _ _)
             (and
              (unfold-this-one? id xs)
              (for/set: : (Setof -Res) ([res (invert-e M σ id xs)])
                (match-define (-Res (? -e? e*) ψs) res)
                (define ψs* ; strengthen with induction hypotheses
                  (for/fold ([ψs* : -es ψs]) ([args (find-calls e* id)])
                    (define hyp
                      (for/fold ([hyp : -e e₀]) ([x xs] [arg args])
                        (e/ hyp x arg)))
                    (set-add ψs* hyp)))
                (-Res e* ψs*)))]
            [_ #f])]
         [(? set? reses)
          (for/set: : (Setof -Res) ([res reses])
            (match-define (cons (cons f* xs*) ψs) res)
            (-Res (apply -?@ f* xs*) ψs))])]
      [_ #|TODO just this for now|# #f]))

  (: go* : (Listof -e) → (Option (Setof (Pairof (Listof -e) -es))))
  (define (go* es)
    (match es
      ['() #f]
      [(cons e es*)
       (match (go e)
         [#f
          (match (go* es*)
            [#f #f]
            [(? set? reses)
             (for/set: : (Setof (Pairof (Listof -e) -es)) ([res reses])
               (match-define (cons es** ψs) res)
               (cons (cons e es**) ψs))])]
         [(? set? reses)
          (for/set: : (Setof (Pairof (Listof -e) -es)) ([res reses])
            (match-define (-Res (? -e? #|FIXME|# e*) ψs) res)
            (cons (cons e* es*) ψs))])]))

  (go e₀))

(: ⇓₁ : -M -σ -Γ -e → (Values -e -Γ))
;; Unfold/evaluate expression only if there's only 1 branch 
(define (⇓₁ M σ Γ e)

  (: go : -Γ -e → (Values -e -Γ))
  (define (go Γ e)
    (match e
      [(-@ f xs _)
       (define-values (fxs* Γ*) (go* Γ (cons f xs)))
       (match-define (cons f* xs*) fxs*)
       (match f*
         [(-ref id _ _)
          (define reses*
            (for*/set: : (Setof (Pairof -e -Γ))
                       ([res (invert-e M σ id xs*)]
                        [ψs (in-value (-Res-facts res))]
                        [Γ* (in-value (Γ⊓ Γ ψs))] #:when Γ*)
              (cons (assert (-Res-e res)) Γ*)))
          (cond
            [(= 1 (set-count reses*))
             (match-define (cons e* Γ*) (set-first reses*))
             (go Γ* (assert e*))]
            [else (values (assert (apply -?@ f* xs*)) Γ)])]
         [_ (values (assert (apply -?@ f* xs*)) Γ)])]
      [_ (values e Γ)]))

  (: go* : -Γ (Listof -e) → (Values (Listof -e) -Γ))
  (define (go* Γ es)
    (define-values (es↓ Γ*)
      (for/fold ([es↓ : (Listof -e) '()] [Γ : -Γ Γ]) ([e es])
        (define-values (e* Γ*) (go Γ e))
        (values (cons e* es↓) Γ*)))
    (values (reverse es↓) Γ*))
  
  (go Γ e))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Debugging
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin
  (define -app (-ref (-id-local 'app 'Λ) 'Λ #f))
  (define -app-body (-b 'app-body))
  (define -len (-ref (-id-local 'len 'Λ) 'Λ #f))
  (define -len-body (-b 'len-body))
  (define -map (-ref (-id-local 'map 'Λ) 'Λ #f))
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
      (⊔ -σ⊥ (-α.def (-id-local 'app 'Λ)) (-Clo '(l₁ l₂) -app-body -ρ⊥ -Γ⊤))
      (-α.def (-id-local 'len 'Λ)) (-Clo '(l) -len-body -ρ⊥ -Γ⊤))
     (-α.def (-id-local 'map 'Λ)) (-Clo '(f xs) -map-body -ρ⊥ -Γ⊤)))
  (define Mdb
    (⊔
     (⊔
      (⊔
       (⊔
        (⊔
         (⊔ -M⊥ -app-body (-Res -l₂ {set (assert (-?@ -null? -l₁))}))
         -app-body
         (-Res
          (-?@ -cons (-?@ -car -l₁) (-?@ -app (-?@ -cdr -l₁) -l₂))
          {set (assert (-?@ -cons? -l₁))}))
        -len-body
        (-Res (-b 0) {set (assert (-?@ -null? (-x 'l)))}))
       -len-body
       (-Res (-?@ '+ (-b 1) (-?@ -len (-?@ -cdr (-x 'l))))
             {set (assert (-?@ -cons? (-x 'l)))}))
      -map-body
      (-Res -null {set (assert (-?@ -null? -xs))}))
     -map-body
     (-Res (-?@ -cons (-?@ -f (-?@ -car -xs)) (-?@ -map -f (-?@ -cdr -xs)))
           {set (assert (-?@ -cons? -xs))}))))
