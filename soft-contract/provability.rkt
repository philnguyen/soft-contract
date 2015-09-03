#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "utils.rkt" "lang.rkt" "runtime.rkt")
(provide Γ⊢V∈C Γ⊢oW Γ⊢e V∈p V≡ Γ⊢e≡
         Γ⊓ Γ⊓e Γ+/-W Γ+/-W∈W spurious? or-R not-R decide-R
         -R)

;; Provability result
(define-type -R (U '✓ 'X '?))

(define Γ⊢ₑₓₜ : (Parameterof (-Γ -e → -R))
  (make-parameter (λ (Γ e) (log-error "external solver not set") '?)))

(: Γ-defines? : -Γ Symbol → Boolean)
;; Check whether the variable is defined in given environment
(define (Γ-defines? Γ x)
  (for/or ([e Γ]) (∋ (FV e) x)))

(: Γ⊢V∈C : -Γ -WV -WV → -R)
(define (Γ⊢V∈C Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (or-R (V∈V V C) (Γ⊢e Γ (-?@ e_c e_v))))

(: Γ⊢oW : -Γ -pred -WV → -R)
;; Check whether value `W` satisfies predicate `p`
(define (Γ⊢oW Γ p W)
  (match-define (-W V e) W)
  (or-R (V∈p V p) (Γ⊢e Γ (-?@ p e))))

(: Γ⊢e : -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (Γ⊢e Γ e)
  (cond
    [e (or-R (Γ⊢₁e Γ e) ((Γ⊢ₑₓₜ) Γ e))]
    [else '?]))

(: Γ⊢₁e : -Γ -e → -R)
(define (Γ⊢₁e Γ e)

  (: ⊢e : -?e → -R)
  ;; Check if expression returns truth
  (define ⊢e
    (match-lambda
      ;; values
      [(-b #f) 'X]
      [(? -•?) '?]
      [(? -v?) '✓]
      ;; constructors
      [(or (? -μ/c?) (? -->i?) (? -x/c?) (? -struct/c?)) '✓]
      ;; special cases
      [(-@ (or '= 'equal?) (list e e) _) '✓]
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
                      (equal? '✓ (Γ⊢e Γ (-?@ 'integer? ei))))
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
                      (equal? '✓ (Γ⊢e Γ (-?@ 'real? ei))))
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
      [(-@ (or (? -pred?) (? -st-ac?)) (list e) _) '?]
      [(-@ (? -o?) _ _) '✓] ; happens to be so for now
      [_ '?]))

  (: e⊢e : -?e -?e → -R)
  ;; Check if `e₂` returns truth when `e₁` does
  (define (e⊢e e₁ e₂)
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

  (define ans
    (or-R (⊢e e)
          (for*/fold ([R : -R '?])
                     ([e₀ Γ] #:when (equal? '? R)
                      [R* (in-value (e⊢e e₀ e))])
            R*)))
  (dbg '⊢ "~a ⊢ ~a : ~a~n" (show-Γ Γ) (show-e e) ans)
  ans)

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

(: ⊢V : -V → -R)
;; Check whether value represents truth
(define ⊢V
  (match-lambda
    [(-b #f) 'X]
    ['• '?]
    [_ '✓]))

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

(: Γ⊢e≡ : -Γ -?e -?e → -R)
(define (Γ⊢e≡ Γ e₁ e₂)
  (cond ; TODO: just this for now
    [(and e₁ e₂) (decide-R (equal? e₁ e₂))]
    [else '?]))

(: V≡ : -V -V → -R)
;; Check whether 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (decide-R (equal? x₁ x₂))]
   [(_ _) '?]))

(: spurious? : -Γ -WVs → Boolean)
;; Check whether `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (safe answer)
(define (spurious? Γ W)

  (: spurious*? : -?e -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(-St id αs)
            (equal? 'X (Γ⊢e Γ (-?@ (-st-mk id (length αs)) e)))]
           [(or (? -Clo?) (? -Ar?) (? -o?))
            (equal? 'X (Γ⊢e Γ (-?@ 'procedure? e)))]
           [(-b (? p?))
            (equal? 'X (Γ⊢e Γ (-?@ 'p? e)))] ...
           [(or (? -=>i?) (? -St/C?) (? -μ/C?) (? -X/C?))
            (for/or : Boolean ([p : -o '(procedure? p? ...)])
              (equal? '✓ (Γ⊢e Γ (-?@ p e))))]
           ['undefined
            (match e
              [(-x x) (Γ-defines? Γ x)]
              [_ #f])]
           ['•
            (match e
              [(-not e*) (equal? '✓ (Γ⊢e Γ e*))]
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

(: Γ+/-W : -Γ -WV → (Values (Option -Γ) (Option -Γ)))
;; Like `(Γ ⊓ W)` and `(Γ ⊓ ¬W)`, probably faster
(define (Γ+/-W Γ W)
  (match-define (-W V e) W)
  (define proved (or-R (⊢V V) (Γ⊢e Γ e)))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))

(: Γ+/-W∈W : -Γ -WV -WV → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `V∈P` and `V∉P`
(define (Γ+/-W∈W Γ W_V W_P)
  (match-define (-W V e_v) W_V)
  (match-define (-W P e_p) W_P)
  (define ψ (-?@ e_p e_v))
  (define proved (or-R (V∈V V P) (Γ⊢e Γ ψ)))
  (values (if (equal? 'X proved) #f (Γ+ Γ ψ))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not ψ)))))

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

(: not-R : -R → -R)
;; Negate provability result
(define not-R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

;; Use the first definite result
(define-syntax or-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (match R₁ ['? (or-R R ...)] [ans ans])]))

(: decide-R : Boolean → -R)
(define decide-R (match-lambda [#t '✓] [#f 'X]))
