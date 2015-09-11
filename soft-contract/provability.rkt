#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "utils.rkt" "lang.rkt" "runtime.rkt")
(provide MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢e V∈p V≡ MσΓ⊢e≡
         Γ⊓ Γ+/-W Γ+/-W∈W spurious? or-R not-R decide-R
         -R
         ;; debugging
         MσΓ⊢₁e Γ⊢e)

(define Γ⊢ₑₓₜ : (Parameterof (-M -σ -Γ -e → -R))
  (make-parameter (λ (M σ Γ e) (log-warning "external solver not set") '?)))

(: MσΓ⊢V∈C : -M -σ -Γ -WV -WV → -R)
;; Check whether value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (or-R (V∈V V C) (MσΓ⊢e M σ Γ (-?@ e_c e_v))))

(: MσΓ⊢oW : -M -σ -Γ -pred -WV → -R)
;; Check whether value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p W)
  (match-define (-W V e) W)
  (or-R (V∈p V p) (MσΓ⊢e M σ Γ (-?@ p e))))

(: MσΓ⊢e : -M -σ -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢e M σ Γ e)
  (cond
    [e (or-R (MσΓ⊢₁e M σ Γ e) ((Γ⊢ₑₓₜ) M σ Γ e))]
    [else '?]))

(: MσΓ⊢₁e : -M -σ -Γ -e → -R)
;; Check if `e` evals to truth given `M`, `σ`, `Γ`
(define (MσΓ⊢₁e M σ Γ e)
  (Γ⊢e Γ e))

(: MσΓ⊢e≡ : -M -σ -Γ -?e -?e → -R)
(define (MσΓ⊢e≡ Γ M σ e₁ e₂)
  (match* (e₁ e₂)
    [((-b b₁) (-b b₂)) (decide-R (equal? b₁ b₂))]
    [(_ _) '?])) ; TODO just this for now

(: spurious? : -M -σ -Γ -WVs → Boolean)
;; Check whether `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (safe answer)
(define (spurious? M σ Γ W)

  (: spurious*? : -?e -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(-St id αs)
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ (-st-mk id (length αs)) e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'p? e)))] ...
           [(or (? -=>i?) (? -St/C?) (? -μ/C?) (? -X/C?))
            (for/or : Boolean ([p : -o '(procedure? p? ...)])
              (equal? '✓ (MσΓ⊢e M σ Γ (-?@ p e))))]
           ['undefined
            (match e
              [(-x x) (Γ-defines? Γ x)]
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

(: unfold : -M -σ -Γ -id (Listof -e) → (Setof -Γ))
;; Unfold (f e …) and attach them to `Γ`, discarding obvious inconsistency
(define (unfold M σ Γ id args)
  ;; TODO: if `id` is wrapped, there's a difference!!
  (for/fold ([acc : (Setof -Γ) ∅])
            ([defn (σ@ σ (-α.def id))])
    (match defn
      [(-Clo xs e _ _)
       (cond
         [(list? xs)
          (for*/fold ([acc : (Setof -Γ) acc])
                     ([res (hash-ref M e)]
                      [e_a (in-value (-Res-e res))] #:when e_a
                      [Γ_a (in-value (-Res-Γ res))])
            (define e_a*
              (for/fold ([e* : -e e_a]) ([x xs] [arg args])
                (e/ e* x arg)))
            (define Γ_a*
              (for/fold ([Γ* : -Γ Γ_a]) ([x xs] [arg args])
                (Γ/ Γ* x arg)))
            (define Γ*
              (for/fold ([Γ* : (Option -Γ) (Γ⊓e Γ e_a*)])
                        ([e Γ_a*])
                (and Γ* (Γ⊓e Γ* e))))
            (cond [Γ* (set-add acc Γ*)]
                  [else acc]))]
         [else acc])]
      [(? -o? o)
       (define Γ* (Γ⊓e Γ (apply -?@ o args)))
       (if Γ* (set-add acc Γ*) acc)])))


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
        ;; constructors
        [(or (? -μ/c?) (? -->i?) (? -x/c?) (? -struct/c?)) '✓]
        ;; special cases
        [(-@ (or '= 'equal?) (list e₁ e₂) _)
         (match* (e₁ e₂)
           [((-b b₁) (-b b₂)) (decide-R (equal? e₁ e₂))]
           [(_ _) '?])] ; TODO just this for now
        ;; negation
        [(-not e*) (not-R (⊢e e*))]
        ;; ariths
        [(-@ 'integer? (list e*) _)
         (match e*
           [(-b b) (decide-R (real? b))]
           [(-@ o (list es ...) _)
            (match o
              [(or 'string-length #|TODO|# 'round 'floor 'ceiling) '✓]
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
              [(or 'string-length 'round 'floor 'ceiling) '✓]
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
              [(or 'string-length 'round 'floor 'ceiling '+ '- '* 'add1 'sub1 'abs)
               '✓]
              [(or (? -pred?) (? -st-mk?)) 'X]
              [_ '?])]
           [_ '?])]
        [(-@ 'boolean? (list e*) _)
         (match e*
           [(-b b) (decide-R (boolean? b))]
           [(-@ (? -pred?) _ _) '✓]
           [(-@ (? -st-mk?) _ _) 'X]
           [_ '?])]
        [(-@ (or (? -pred?) (? -st-ac?)) (list e) _) '?]
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
              [(truth-pred? p) '✓]
              [(equal? p 'not) 'X]
              [else '?])]
           [(_ _) '?])]
        [(_ R) R]))
    (dbg 'e⊢e "~a ⊢ ~a : ~a~n~n" (show-e e₁) (show-e e₂) ans)
    ans)
  
  (define ans
    (cond
      [e
       (or-R (⊢e e)
             (for*/fold ([R : -R '?])
                        ([e₀ Γ] #:when (equal? '? R)
                         [R* (in-value (e⊢e e₀ e))])
               R*))]
      [else '?]))
  (dbg '⊢ "~a ⊢ ~a : ~a~n~n"(show-Γ Γ) (show-?e e) ans)
  ans)

(: ⊢V : -V → -R)
;; Check whether value represents truth
(define ⊢V
  (match-lambda
    [(-b #f) 'X]
    ['• '?]
    [_ '✓]))

(: V∈V : -V -V → -R)
;; Check whether value satisfies predicate
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
;; Check whether value satisfies predicate
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
      [else
       (match-define (-st-p id n) p)
       (match V
         [(-St id* _) (decide-R (equal? id id*))]
         ['• '?]
         [_ 'X])]))
  (with-prim-checks integer? real? number? not boolean? string? symbol? keyword?))

(: V≡ : -V -V → -R)
;; Check whether 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (decide-R (equal? x₁ x₂))]
   [(_ _) '?]))

(: Γ-defines? : -Γ Symbol → Boolean)
;; Check whether the variable is defined in given environment
(define (Γ-defines? Γ x)
  (for/or ([e Γ]) (∋ (FV e) x)))

(: truth-pred? : -pred → Boolean)
;; Does `(p? x)` imply `x` eval to truth?
(define (truth-pred? p)
  (case p
    [(not boolean?) #f]
    [else #t]))

(: p⇒p : -pred -pred → -R)
(define (p⇒p p q)
  (cond
    [(equal? p q) '✓]
    [else
     (match* (p q)
       ; structs
       [((-st-p t _) (-st-p t _)) '✓]
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

(: Γ⊓ : -Γ -Γ → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (Γ⊓ Γ₀ Γ₁)
  (for/fold ([Γ : (Option -Γ) Γ₀]) ([e Γ₁])
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

(: invert : -M -σ -id (Listof -e) → (Setof -Res))
;; Given proposition `(p? v)`, generate an overapproximation of expressions
;; that could have evaluated to it
(define (invert M σ f args)

  (match f
    [(-ref id _)
     (define α (-α.def id))
     (match/nd: (-V → -Res) (σ@ σ α)
       [(or (-Clo (? list? xs) e _ _) (-Clo* (? list? xs) e _))
        ;; Convert invariant about parameters into one about arguments
        (define (convert [e : -e]) : -e
          (for/fold ([e : -e e]) ([x (assert xs)] [arg args])
            (e/ e x arg)))
        
        (match/nd: (-Res → -Res) (hash-ref M (assert e))
          [(-Res e-xs Γ-xs)
           (define e-args (and e-xs (convert e-xs)))
           (define Γ-args (for/set: : -Γ ([e Γ-xs]) (convert e)))
           (-Res e-args Γ-args)])]
        
       [_ -Res⊤])]
    [_
     ; imprecise for now
     (set -Res⊤)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Debugging
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin
  (define edb (-@ (-ref (-id 'list? 'Λ) 'phil) (list (-x 'arg)) 'Λ))
  (define Γdb : -Γ {set edb})
  (define σdb (⊔ -σ⊥ (-α.def (-id 'list? 'Λ)) (-Clo '(z) (-b 'arbitrary) -ρ⊥ -Γ⊤)))
  (define Mdb
    (⊔
     (⊔
      (⊔ -M⊥ (-b 'arbitrary) (-Res (-b #t) (Γ+ -Γ⊤ (-?@ (-st-p (-id 'null 'Λ) 0) (-x 'z)))))
      (-b 'arbitrary)
      (-Res (-b #f) (Γ+ -Γ⊤ (-not (-?@ (-st-p (-id 'null 'Λ) 0) (-x 'z))) (-not (-?@ (-st-p (-id 'cons 'Λ) 0) (-x 'z))))))
     (-b 'arbitrary)
     (-Res (-?@ (-ref (-id 'list? 'Λ) 'phil) (-?@ -cdr (-x 'z))) (Γ+ -Γ⊤ (-?@ -cons? (-x 'z)))))))
