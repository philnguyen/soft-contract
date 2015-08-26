#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
#;(provide defines? all-prove? all-refute? some-proves? some-refutes?
         ⊢ Γ⊢ Γ⊢₀ Γ⊢ₑₓₜ σ⊢)
(provide Γ⊢V∈C Γ⊢oW Γ⊢e e⊢e ⊢e V∈p V≡ Γ⊢e≡
         split-Γ split-Γ/Ve spurious? or-R not-R decide-R)

(define Γ⊢ₑₓₜ : (Parameterof (-Γ -e → -R))
  (make-parameter (λ (Γ e)
                    (log-error "external solver not set")
                    '?)))

(: Γ⊢V∈C : -Γ -WV -WV → -R)
(define (Γ⊢V∈C Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (or-R (V∈V V C) (Γ⊢e Γ (-?@ e_c (list e_v)))))

(: Γ⊢oW : -Γ -pred -WV → -R)
;; Check whether value `W` satisfies predicate `p`
(define (Γ⊢oW Γ p W)
  (match-define (-W V e) W)
  (or-R (V∈p V p) (Γ⊢e Γ e)))

(: Γ⊢e : -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (Γ⊢e Γ e)
  (cond
    [e
     (or-R
      ; TODO: can't use `for/first` in TR
      (for*/fold ([R : -R (⊢e e)])
                 ([e* Γ]
                  #:when (equal? '? R)
                  [R* (in-value (e⊢e e* e))])
        R*)
      ((Γ⊢ₑₓₜ) Γ e))]
    [else '?]))

(: e⊢e : -?e -?e → -R)
;; Check if `e₂` returns truth when `e₁` does
(define (e⊢e e₁ e₂)
  (match* ((⊢e e₁) (⊢e e₂))
    [('X _) '✓]
    [(_ '?)
     (match* (e₁ e₂)
       ; e ⇒ e
       [(e e) '✓]
       ; ¬e₁⇒¬e₂ ≡ e₂⇒e₁
       [((-not e₁*) (-not e₂*))
        (e⊢e e₂* e₁*)]
       ; 
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
    ;; ariths
    [(-@ (? -o? o) xs _)
     (match o
       ['not (not-R (⊢e (car xs)))]
       [(? -pred?) '?]
       [_ '✓])]
    [_ '?]))

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
         [(or (? -o?) (? -Clo?) (? -Ar?)) '✓]
         ['• '?]
         [_ 'X])]
      [else
       (match-define (-st-p id n) p)
       (match V
         [(-St id* _) (decide-R (equal? id id*))]
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

(: spurious? : -Γ -?e (U -V -Vs) → Boolean)
;; Check whether `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (safe answer)
(define (spurious? Γ e V)
  (cond
    [(list? V)
     (match e
       [(-@ 'values es _)
        (implies
         (= (length es) (length V))
         (for/or : Boolean ([ei es] [Vi V])
           (spurious? Γ ei Vi)))]
       [_ #f])]
    [else
     (define-syntax-rule (with-prim-checks p? ...)
       (cond
         [e
          (match V
            [(-St id αs)
             (equal? 'X (Γ⊢e Γ (-?@ (-st-mk id (length αs)) (list e))))]
            [(or (? -Clo?) (? -Ar?) (? -o?))
             (equal? 'X (Γ⊢e Γ (-?@ 'procedure? (list e))))]
            [(-b (? p?))
             (equal? 'X (Γ⊢e Γ (-?@ 'p? (list e))))] ...
            [(or (? -=>i?) (? -St/C?) (? -μ/C?) (? -X/C?))
             (for/or : Boolean ([p : -o '(procedure? p? ...)])
               (equal? '✓ (Γ⊢e Γ (-?@ p (list e)))))]
            [_ #f])]
         [else #f]))
     ;; order matters for precision, in the presence of subtypes
     (with-prim-checks integer? real? number? string? symbol? keyword? not boolean?)]))

(: split-Γ : -Γ -V -?e → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `V@e` and `¬(V@e)`
(define (split-Γ Γ V e)
  (define proved (or-R (⊢V V) (Γ⊢e Γ e)))
  (define Γ_t* (if (equal? 'X proved) #f (Γ+ Γ e)))
  (define Γ_f* (if (equal? '✓ proved) #f (Γ+ Γ (-not e))))
  (values Γ_t* Γ_f*))

(: split-Γ/Ve : -Γ -WV -WV → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `V∈P` and `V∉P`
(define (split-Γ/Ve Γ W_V W_P)
  (match-define (-W V e_v) W_V)
  (match-define (-W P e_p) W_P)
  (define ψ (-?@ e_p (list e_v)))
  (define proved (or-R (V∈V V P) (Γ⊢e Γ ψ)))
  (define Γ_t* (if (equal? 'X proved) #f (Γ+ Γ ψ)))
  (define Γ_f* (if (equal? '✓ proved) #f (Γ+ Γ (-not ψ))))
  (values Γ_t* Γ_f*))

(: not-R : -R → -R)
;; Negate provability result
(define not-R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

;; Use the first definite result
(define-syntax or-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...) (match R₁ ['? (or-R R ...)] [ans ans])]))

(: decide-R : Boolean → -R)
(define decide-R (match-lambda [#t '✓] [#f 'X]))
