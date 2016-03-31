#lang typed/racket/base

(provide Γ⊢ₑₓₜ Γ⊢e partition-Γs ⊢V p∋Vs Γ⊓
         ensure-simple-consistency
         plausible-Γ-s? plausible-W? plausible-V-s?)

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../primitives/utils.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         (for-syntax
          racket/base racket/contract
          "../utils/pretty.rkt" 
          "../primitives/utils.rkt"))

;; External solver to be plugged in. Return trivial answer by default.
(define-parameter Γ⊢ₑₓₜ : (-Γ -e → -R)
  (λ (Γ e)
    (printf "Warning: external solver not set~n")
    '?))

;; Syntax generation for checking whether argument satisfies predicate
(begin-for-syntax

  ;; Inspect inner application to see if it satisfies predicate
  (define/contract (generate-app-clauses p zs)
    (identifier? identifier? . -> . (listof syntax?))
    (define ⊢e (datum->syntax zs '⊢e))
    (define p⇒p (datum->syntax zs 'p⇒p))

    (for/list ([(o o-rng) prim-ranges])

      ;; Default case: application's range matches predicate exactly
      (define main-clause #`[(#,o-rng) '✓])
      
      ;; Refined cases: predicate is more refined than application's coarsest range
      (define/contract refined-clauses (listof syntax?)
        (for/list ([(o-rng* o-doms) (hash-ref prim-refinements-for-ranges o (hasheq))])
          
          (define/contract args (listof identifier?)
            (for/list ([(_ i) (in-indexed o-doms)])
              (datum->syntax #f (format-symbol "x~a" (n-sub i)))))
          
          (define/contract preconds (listof syntax?)
            (for/list ([dom o-doms] [arg args])
              #`(eq? '✓ (#,⊢e (-@ '#,dom (list #,arg) 0)))))
          
          #`[(#,o-rng*)
             (match #,zs
               [(list #,@args) (if (and #,@preconds) '✓ '?)]
               [_ '?])]))

      (define rhs
        (cond
          [(null? refined-clauses)
           #`(#,p⇒p '#,o-rng #,p)]
          [else
           #`(match (#,p⇒p '#,o-rng #,p)
               ['?
                (case #,p
                  #,@refined-clauses
                  [else '?])]
               [ans ans])]))
      #`[(#,o) #,rhs])))

;; Check whether predicate excludes boolean
(define boolean-excludes? : (Symbol → Boolean)
  (set->predicate (hash-ref exclusions 'boolean?)))

(: Γ⊢e : -Γ -s → -R)
;; Check if `e` evals to truth given `M`
(define (Γ⊢e Γ e)
  (match-define (-Γ φs _ _) Γ)
  
  ;; It's not always desirable to have rule `{… #f …} ⊢ e : ✓`, because
  ;; sometimes we want `{… #f …} ⊢ (¬ e) : ✓`, which means `{… #f …} ⊢ e : ✗`
  ;; This is a problem with precision rather than soundness, but I want
  ;; (obviously) inconsistent path-conditions to not exist in the first place.
  (when (∋ φs -ff)
    (error 'Γ⊢e "Attempt to prove/refute with inconsistent path-condition"))

  (: ⊢e : -e → -R)
  ;; Check if expression returns truth
  (define (⊢e e)
    (match e
      [(-b b) (if b '✓ '✗)]
      [φ #:when (∋ φs φ) '✓]
      [φ #:when (∋ φs (-not φ)) '✗]
      [(? -•?) '?]
      [(? -v?) '✓]
      [(-@ f xs _) (⊢@ f xs)]
      [_ '?]))

  (: ⊢@ : -e (Listof -e) → -R)
  ;; Check if application returns truth
  (define (⊢@ p xs)

    ;; generate clauses checking if `(p xs)` returns truth
    (define-syntax (generate-predicate-clauses stx)
      (define ans
        #`(match xs
            [(list (? -b? b))
             (match (-?@ p b)
               [(-b x) (decide-R (and x #|force boolean|# #t))]
               [_ '?])]
            [(list (-@ o zs _))
             (case o
               #,@(generate-app-clauses #'p #'zs)
               [else
                (cond
                  [(and (-st-mk? o) (base? p)) '✗]
                  [else '?])])]
            [_ '?]))
      ;(printf "generated:~n~a~n" (pretty (syntax->datum ans)))
      ans)

    (match p
      [(? -st-mk?) '✓]
      [(-st-p si)
       (match xs
         [(list (-@ (-st-mk sj) _ _)) ; TODO: No sub-struct for now.
          (decide-R (equal? si sj))]
         [(list (-b _)) '✗]
         [(list (-@ (? symbol? f) _ _))
          (cond ;; HACK for now
            [(hash-ref prim-ranges f #f)
             =>
             (λ ([f-rng : Symbol])
               (cond
                 [(∋ (set 'integer? 'real? 'number? 'vector? 'boolean? 'not 'null?) f-rng) '✗]
                 [else '?]))]
            [else '?])]
         [_ '?])]
      ['not (not-R (⊢e (car xs)))] ; assume right arity
      ['any/c '✓]
      ['none/c '✗]
      [(or 'equal? '=)
       (match xs
         [(list e₁ e₂)
          (match* (e₁ e₂)
            [((? -λ? v₁) (? -λ? v₂)) ; can't compare higher-order literals
             (if (equal? v₁ v₂) '? '✗)]
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
                  (eq? '✓ (⊢e (-@ 'equal? (list f g) 0))))
                 (= (length xs) (length ys)))
                (define res
                  (for/set: : (℘ -R) ([x xs] [y ys])
                    (⊢e (-@ 'equal? (list x y) 0))))
                (cond
                  [(or (set-empty? res) (equal? res {set '✓})) '✓]
                  [(and (-st-mk? f) (∋ res '✗)) '✗]
                  [else '?])]
               [else '?])]
            [(_ _) (if (equal? e₁ e₂) '✓ '?)])]
         [_ #|TODO|# '?])]
      [(? symbol?)
       (cond
         [(and (eq? p 'boolean?) (match? xs (list (-@ (? -st-p?) _ _)))) '✓]
         [(and (eq? p 'procedure?) (match? xs (list (or (? -λ?) (? -case-λ?))))) '✓]
         [(hash-ref prim-ranges p #f) =>
          (λ ([p-rng : Symbol])
            (cond
              [(boolean-excludes? p-rng) '✓]
              [else (generate-predicate-clauses)]))]
         [else '?])]
      
      [_ '?]))

  (: e⊢e : -e -e → -R)
  ;; Check if `e₂` returns truth when `e₁` does
  (define (e⊢e e₁ e₂)
    (with-debugging/off
      ((ans)
       (match* ((⊢e e₁) (⊢e e₂))
         [('✗ _) '✓]
         [(_ '?)
          (match* (e₁ e₂)
            ; e ⇒ e
            [(e e) '✓]
            ; NOTE: Don't abuse "contrapositive"
            ; (¬e₁ ⊢ ¬e₂ : ✗) does not follow from (e₂ ⊢ e₁ : ✗)
            [((-not e₁*) (-not e₂*))
             (case (e⊢e e₂* e₁*)
               [(✓)   '✓]
               [(✗ ?) '?])]
            [(e₁ (-not e₂*))
             (not-R (e⊢e e₁ e₂*))]
            [((-@ (? -o? p) (list e) _) (-@ (? -o? q) (list e) _))
             (p⇒p p q)] ; FIXME
            [((-@ (? -o? p) (list e) _) e)
             (cond
               [(eq? 'not p) '✗]
               [(and (symbol? p) (boolean-excludes? p)) '✓]
               [(-st-p? p) '✓]
               [else '?])]
            [((-@ (or '= 'equal?) (list e₁ e₂) _) (-@ (? -o? p) (list e₁) _))
             (⊢@ p (list e₂))]
            [((-@ (or '= 'equal?) (list e₁ e₂) _) (-@ (? -o? p) (list e₂) _))
             (⊢@ p (list e₁))]
            [(_ _) '?])]
         [(_ R) R]))
      (printf "~a ⊢ ~a : ~a~n~n" (show-e e₁) (show-e e₂) ans)))

  (with-debugging/off
    ((ans)
     (cond
       [e
        (first-R
         (⊢e e)
         (for*/fold ([R : -R '?])
                    ([e₀ φs] #:when (eq? '? R)
                     [R* (in-value (e⊢e e₀ e))])
           R*)
         ((Γ⊢ₑₓₜ) Γ e))]
       [else '?]))
    (printf "~a ⊢ ~a : ~a~n" (show-Γ Γ) (show-s e) ans)))

(: plausible-Γ-s? : -Γ -s → Boolean)
(define (plausible-Γ-s? Γ s)
  (not (eq? '✗ (Γ⊢e Γ s))))

(: plausible-W? : -Γ (Listof -V) -s → Boolean)
;; Check if value(s) `Vs` can instantiate symbol `s` given path condition `Γ`
;; - #f indicates a definitely bogus case
;; - #t indicates (conservative) plausibility
(define (plausible-W? Γ Vs s)
  (match* (Vs s)
    [(_ (-@ 'values es _))
     (and (= (length Vs) (length es))
          (for/and : Boolean ([V Vs] [e es])
            (plausible-V-s? Γ V e)))]
    [((list V) _) #:when s
     (plausible-V-s? Γ V s)]
    [(_ (or (? -v?) (-@ (? -prim?) _ _))) #f] ; length(Vs) ≠ 1, length(s) = 1
    [(_ #f) #t]))

(: plausible-V-s? : -Γ -V -s → Boolean)
(define (plausible-V-s? Γ V s)
  (define-syntax-rule (with-prim-checks p? ...)
    (cond
      [s
       (match V
         [(or (-St si _) (-St* si _ _ _)) #:when si
          (plausible-Γ-s? Γ (-?@ (-st-p si) s))]
         [(or (? -Vector?) (? -Vector/hetero?) (? -Vector/homo?))
          (plausible-Γ-s? Γ (-?@ 'vector? s))]
         [(or (? -Clo?) (? -Ar?) (? -o?))
          (plausible-Γ-s? Γ (-?@ 'procedure? s))]
         [(-b (? p?))
          (and (plausible-Γ-s? Γ (-?@ 'p? s))
               (implies (-b? s) (equal? V s)))] ...
         [(or (? -=>_?) (? -St/C?) (? -x/C?))
          (for/and : Boolean ([p : -o '(procedure? p? ...)])
            (case (Γ⊢e Γ (-?@ p s))
              [(✓)   #f]
              [(✗ ?) #t]))]
         ['undefined
          (case (Γ⊢e Γ (-?@ 'defined? s))
            [(✗ ?) #t]
            [(✓)   #f])]
         [(-●)
          (match s
            [(-not s*)
             (case (Γ⊢e Γ s*)
               [(✗ ?) #t]
               [(✓)   #f])]
            [_ #t])]
         [_ #t])]
      [else #t]))
  
  ;; order matters for precision, in the presence of subtypes
  (with-prim-checks integer? real? number? string? symbol? keyword? not boolean?))

(: Γ⊓ : -Γ -Γ → (Option -Γ))
;; Join 2 path conditions, eliminating obvious inconsistencies
(define (Γ⊓ Γ₀ Γ₁)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (define Γ₀*
    (for/fold ([Γ₀ : (Option -Γ) Γ₀]) ([φ₁ φs₁])
      (and Γ₀
           (case (Γ⊢e Γ₀ φ₁)
             [(✓ ?) (Γ+ Γ₀ φ₁)]
             [(✗)   #f]))))
  (match Γ₀* ; note that `γs₁` are added without checking
    [(-Γ φs₀ as₀ γs₀) (-Γ φs₀ as₀ (∪ γs₀ γs₁))]
    [#f #f]))

(: partition-Γs : (℘ (Pairof -Γ -s))
                → (Values (℘ (Pairof -Γ -s)) (℘ (Pairof -Γ -s)) (℘ (Pairof -Γ -s))))
;; Partition set of ⟨path-condition, proposition⟩ pairs by provability
(define (partition-Γs ps)
  (define-set ✓s : (Pairof -Γ -s))
  (define-set ✗s : (Pairof -Γ -s))
  (define-set ?s : (Pairof -Γ -s))
  (for ([p ps])
    (match-define (cons Γ s) p)
    (case (Γ⊢e Γ s)
      [(✓) (✓s-add! p)]
      [(✗) (✗s-add! p)]
      [(?) (?s-add! p)]))
  (values ✓s ✗s ?s))

(: ⊢V : -V → -R)
;; Check if value represents truth
(define ⊢V
  (match-lambda
    [(-b #f) '✗]
    [(-●) '?]
    [_ '✓]))

(: p∋Vs : -V -V * → -R)
;; Check if value satisfies predicate
(define (p∋Vs p . Vs)
  
  (define (check-proc-arity-1 [V : -V]) : -R
    (match (p∋Vs 'procedure? V)
      ['✓ (decide-R (arity-includes? (assert (V-arity V)) 1))]
      [ans ans]))

  (match p
    [(? -st-mk?) '✓]
    [(? -st-mut?) '✓]
    [(? -st-ac?) '✓]
    [(-st-p si)
     (match Vs
       [(list (or (-St sj _) (-St* sj _ _ _)))
        ;; TODO: no sub-struct for now. May change later.
        (decide-R (equal? si (assert sj)))]
       [(list (-●)) '?]
       [_ '✗])]
    [(? symbol?)
     (case p
       ;; Insert manual rules here
       [(procedure?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -o?) (? -Clo?) (? -Ar?) (? -Not/C?))) '✓]
          [(list (or (-And/C flat? _ _) (-Or/C flat? _ _) (-St/C flat? _ _))) (decide-R flat?)]
          [_ '✗])]
       [(vector?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -Vector?) (? -Vector/hetero?) (? -Vector/homo?))) '✓]
          [_ '✗])]
       [(contract?)
        (match Vs
          [(list (or (? -=>_?) (? -And/C?) (? -Or/C?) (? -Not/C?)
                     (? -Vectorof?) (? -Vector/C?) (? -St/C?) (? -x/C?))) '✓]
          [(list V) (check-proc-arity-1 V)]
          [_ '?])]
       [(flat-contract?)
        (match Vs
          [(list V) (check-proc-arity-1 V)]
          [_ '?])]
       [(any/c) '✓]
       [(none/c) '✗]
       [(arity-includes?)
        (match Vs
          [(list (-b (? Arity? a)) (-b (? Arity? b)))
           (decide-R (arity-includes? a b))]
          [_ '?])]
       ;; Default rules for operations on base values rely on simplification from `-?@`
       [else
        (cond
          [(hash-ref prim-ranges p #f) =>
           (λ ([p-rng : Symbol]) : -R
             (cond [(boolean-excludes? p-rng) '✓]
                   [else
                    (match Vs
                      [(list (? -b? bs) ...)
                       (match (apply -?@ p (cast bs (Listof -b)))
                         [(-b b) (decide-R (and b #|force boolean|# #t))]
                         [_ '?])]
                      [(list (? -●?) ...) '?]
                      [_ (cond [(and (base? p) (and (match? Vs (list (not (? -b?)))))) '✗]
                               [else '?])])]))]
          [else '?])])]
    [_ '?]))

(: V≡ : -V -V → -R)
;; Check if 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (decide-R (equal? x₁ x₂))]
   [(_ _) '?]))

(: p⇒p : -o -o → -R)
;; Return whether predicate `p` definitely implies or excludes `q`.
(define (p⇒p p q)
  (match* (p q)
    [(_ 'any/c) '✓]
    [('none/c _) '✓]
    [(_ 'none/c) '✗]
    [((? symbol? p) (? symbol? q))
     (cond [(∋ (hash-ref implications p →∅) q) '✓]
           [(∋ (hash-ref exclusions p →∅) q) '✗]
           [else '?])]
    [(p 'values)
     (case p
       [(not) '✗]
       [(any/c) '?]
       [else '✓])]
    [((-st-p si) (-st-p sj))
     ;; TODO: no sub-struct for now. Probably changes later
     (decide-R (equal? si sj))]
    [(_ _)
     (cond [(or (and (symbol? p) (hash-has-key? implications p) (-st-p? q))
                (and (symbol? q) (hash-has-key? implications q) (-st-p? p)))
            '✗]
           [else '?])]))

(: ensure-simple-consistency : (Option -Γ) → (Option -Γ))
;; Throw away obviously inconsistent path-condition
(define (ensure-simple-consistency Γ)
  (match Γ
    [(-Γ φs as γs)
     (define-values (plausible? _)
       (for/fold ([plausible? : Boolean #t] [Γ : -Γ (-Γ ∅ as γs)])
                 ([φ φs])
         (values (plausible-Γ-s? Γ φ) (Γ+ Γ φ))))
     (and plausible? Γ)]
    [#f #f]))


(module+ test
  (require typed/rackunit
           "../ast/definition.rkt"
           "../runtime/main.rkt"
           "for-test.rkt")
  
  ;; V ∈ p
  (check-✓ (p∋Vs 'not (-b #f)))
  (check-✓ (p∋Vs 'boolean? (-b #f)))
  (check-✓ (p∋Vs 'integer? (-b 1)))
  (check-✓ (p∋Vs 'real? (-b 1)))
  (check-✓ (p∋Vs 'number? (-b 1)))
  (check-✓ (p∋Vs 'procedure? (-Clo '(x) (λ _ (⊥ans)) ⊥ρ ⊤Γ)))
  (check-✓ (p∋Vs 'procedure? 'procedure?))
  (check-✓ (p∋Vs -cons? (-St -s-cons (list (-α.fld 0 0 0) (-α.fld 0 0 1)))))
  (check-✗ (p∋Vs 'number? (-St -s-cons (list (-α.fld 0 0 0) (-α.fld 0 0 1)))))
  (check-✗ (p∋Vs 'integer? (-b 1.5)))
  (check-✗ (p∋Vs 'real? (-b 1+1i)))
  (check-? (p∋Vs 'integer? -●/V))

  ;; ⊢ e
  (check-✓ (Γ⊢e ⊤Γ 'not))
  (check-✓ (Γ⊢e ⊤Γ (-b 0)))
  (check-✗ (Γ⊢e ⊤Γ (-b #f)))
  (check-? (Γ⊢e ⊤Γ (-x 'x)))
  (check-✗ (Γ⊢e ⊤Γ (-?@ 'not (-b 0))))
  (check-✓ (Γ⊢e ⊤Γ (-?@ 'equal? (-x 'x) (-x 'x))))
  (check-✓ (Γ⊢e ⊤Γ (-?@ '+ (-x 'x) (-x 'y))))
  (check-✗ (Γ⊢e ⊤Γ (-?@ -cons? -null)))
  (check-✗ (Γ⊢e ⊤Γ (-?@ 'null? (-?@ -cons (-b 0) (-b 1)))))
  
  ;; Γ ⊢ e
  (check-✓ (Γ⊢e (Γ+ ⊤Γ (-?@ -cons? (-x 'x))) (-x 'x)))
  (check-✓ (Γ⊢e (Γ+ ⊤Γ (-?@ 'integer? (-x 'x))) (-?@ 'real? (-x 'x))))
  (check-✓ (Γ⊢e (Γ+ ⊤Γ (-?@ 'not (-?@ 'number? (-x 'x))))
                (-?@ 'not (-?@ 'integer? (-x 'x)))))
  (check-✗ (Γ⊢e (Γ+ ⊤Γ (-?@ 'not (-x 'x))) (-x 'x)))
  (check-? (Γ⊢e (Γ+ ⊤Γ (-?@ 'number? (-x 'x)))
                (-?@ 'integer? (-x 'x))))

  ;; plausibility
  (check-false (plausible-W? ⊤Γ (list (-b 1)) (-b 2)))
  (check-false (plausible-W? ⊤Γ (list (-b 1) (-b 2)) (-b 3)))
  (check-false (plausible-W? ⊤Γ (list (-b 1) (-b 2)) (-?@ 'values (-b 1) (-b 3))))
  (check-false (plausible-W? ⊤Γ (list -tt) -ff))
  (check-true  (plausible-W? ⊤Γ (list -tt) -tt))
  (check-false (plausible-W? (Γ+ ⊤Γ (-not (-x 'x))) (list (-b 0)) (-x 'x)))
  )
