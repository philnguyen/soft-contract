#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
#;(provide defines? all-prove? all-refute? some-proves? some-refutes?
         ⊢ Γ⊢ Γ⊢₀ Γ⊢ₑₓₜ σ⊢)
(provide Γ⊢oW Γ⊢e e⊢e ⊢e V∈p
         split-Γ spurious?)
#|
(:* all-prove? all-refute? some-proves? some-refutes? : -M -σ -Γ -WVs -WV → Boolean)
(define (all-prove?    M σ Γ Ws W_p) (for/and ([W Ws]) (eq? (⊢ M σ Γ W W_p) '✓)))
(define (all-refute?   M σ Γ Ws W_p) (for/and ([W Ws]) (eq? (⊢ M σ Γ W W_p) 'X)))
(define (some-proves?  M σ Γ Ws W_p) (for/or  ([W Ws]) (eq? (⊢ M σ Γ W W_p) '✓)))
(define (some-refutes? M σ Γ Ws W_p) (for/or  ([W Ws]) (eq? (⊢ M σ Γ W W_p) 'X)))

(: ⊢ : -σ -Γ -WV -WV → -R)
;; Check whether value `W_v` satisfies predicate `W_p` according to `σ` and `Γ`
(define (⊢ σ Γ W_v W_p)
  (match-define (-W V   π  ) W_v)
  (match-define (-W V_p π_p) W_p)
  (match (σ⊢ σ V V_p)
    ['? (if (and π π_p) (Γ⊢ Γ (-π@ π_p (list π))) '?)]
    [a a]))

(: Γ⊢ : -Γ -π* → -R)
;; Check whether syntax `π` always evaluates to non-#f value given assumptions `Γ`
(define (Γ⊢ Γ π)
  (match (Γ⊢₀ Γ π)
    ['? (if π ((Γ⊢ₑₓₜ) Γ π) '?)]
    [r r]))

;; Default (empty) external solver
(define Γ⊢ₑₓₜ : (Parameterof (-Γ -π → -R))
  (make-parameter (λ (Γ π)
                    (log-warning "External solver not set")
                    '?)))

(: Γ⊢₀ : -Γ -π* → -R)
;; Internal simple proof system
(define (Γ⊢₀ Γ π*)

  (: go : -π → -R)
  (define (go π)
    (cond
      [(set-member? Γ π) '✓]
      [(set-member? Γ (-π@ 'not (list π))) 'X]
      [else
       (match π
         [(-b #f) 'X]
         [(? -prim?) '✓]
         [(-π@ π πs)
          (match π ; TODO more sophisticated ones possible, e.g. (int? (+ _ _))
            ['integer?
             (match πs
               [(list (-b (? integer?))) '✓]
               [_ '?])]
            ['real?
             (match πs
               [(list (-b (? real?))) '✓]
               [_ '?])]
            ['number?
             (match πs
               [(list (-b (? number?))) '✓]
               [_ '?])]
            ['not (¬R (Γ⊢₀ Γ (first πs)))]
            ['boolean?
             (match πs
               [(list (-b (? boolean?))) '✓]
               [_ '?])]
            ['string?
             (match πs
               [(list (-b (? string?))) '✓]
               [_ '?])]
            ['symbol?
             (match πs
               [(list (-b (? string?))) '✓]
               [_ '?])]
            ['procedure?
             (match πs
               [(list (-b _)) 'X]
               [_ '?])]
            ['keyword?
             '?]
            ;; TODO all the other ones
            [(or '+ '- '* '/) '✓]
            [_ '?])])]))

  (if π* (go π*) '?))

(: σ⊢ : -σ -V -V → -R)
(define (σ⊢ σ V C)
  (match* (V C)
    [((-b (? integer?)) 'integer?) '✓]
    [((-b (? real?)) 'real?) '✓]
    [((-b (? number?)) 'number?) '✓]
    [((? -Clo?) 'procedure?) '✓]
    [((? -o?)  'procedure?) '✓]
    [((? -Ar?) 'procedure?) '✓]
    [((-St id _) (-st-p id _)) '✓]

    [('• (? -o?)) '?]
    [(_ (? -o?)) 'X]
    [(_ _) '?]))
|#

(: Γ⊢oW : -Γ -pred -WV → -R)
;; Check whether value `W` satisfies predicate `p`
(define (Γ⊢oW Γ p W)
  (match-define (-W V e) W)
  (match* ((V∈p V p) (Γ⊢e Γ e))
    ;; For debugging only
    [('✓ 'X) (error 'Γ⊢oW "inconsistent")]
    [('X '✓) (error 'Γ⊢oW "inconsistent")]
    ;; Valid casees
    [('? '?) '?]
    [('✓ _) '✓]
    [(_ '✓) '✓]
    [('X _) 'X]
    [(_ 'X) 'X]))

(: Γ⊢e : -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (Γ⊢e Γ e)
  (cond
    [e
     ;; TODO: can't use `for/first` in TR
     (for*/fold ([R : -R (⊢e e)])
                ([e* Γ]
                 #:when (equal? '? R)
                 [R* (in-value (e⊢e e* e))])
       R*)]
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
        (¬R (e⊢e e₁ e₂*))]
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
    [(or (? -μ/c?) (? -->?) (? -->i?) (? -x/c?) (? -struct/c?)) '✓]
    ;; special cases
    [(-@ (or '= 'equal?) (list e e) _) '✓]
    ;; ariths
    [(-@ (? -o? o) xs _)
     (match o
       ['not (¬R (⊢e (car xs)))]
       [(? -pred?) '?]
       [_ '✓])]
    [_ '?]))

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

(: spurious? : -Γ -?e -V → Boolean)
;; Check whether `e` cannot evaluate to `V` given `Γ` is true
;;   return #t --> `(e ⇓ V)` is spurious
;;   return #f --> don't know (safe answer)
(define (spurious? Γ e V)
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
         [(or (? -=>?) (? -=>i?) (? -St/C?) (? -μ/C?) (? -X/C?))
          (for/or : Boolean ([p : -o '(procedure? p? ...)])
            (equal? '✓ (Γ⊢e Γ (-?@ p (list e)))))]
         [_ #f])]
      [else #f]))
  ;; order matters for precision, in the presence of subtypes
  (with-prim-checks integer? real? number? string? symbol? keyword? not boolean?))

(: split-Γ : -Γ -V -?e → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `V@e` and `¬(V@e)`
(define (split-Γ Γ V e)
  (define Γ_t (Γ+ Γ e))
  (define Γ_f (Γ+ Γ (-not e)))
  (define e-proved (Γ⊢e Γ e))
  (define Γ_t*
    (match* (e-proved V)
      [('X _) #f]
      [(_ (-b #f)) #f]
      [(_ _) Γ_t]))
  (define Γ_f*
    (match* (e-proved V)
      [('✓ _) #f]
      [(_ (or (-b #f) '•)) Γ_f]
      [(_ _) #f]))
  (values Γ_t* Γ_f*))

(: ¬R : -R → -R)
(define ¬R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

(: decide-R : Boolean → -R)
(define decide-R (match-lambda [#t '✓] [#f 'X]))
