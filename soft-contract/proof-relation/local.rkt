#lang typed/racket/base

(provide es⊢e es⊢ₑₓₜe lite? Γ⊢e partition-Γs ⊢V p∋Vs Γ⊓ es⊓
         φs/ensure-consistency Γ/ensure-consistency
         plausible-es-s? plausible-W? plausible-V-s?)

(require racket/match
         racket/set
         racket/bool
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../primitives/utils.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         (for-syntax
          racket/base racket/contract
          "../utils/pretty.rkt" 
          "../primitives/utils.rkt"))

;; External solver to be plugged in. Return trivial answer by default.
(define-parameter es⊢ₑₓₜe : ((℘ -e) -e → -R)
  (λ _
    (printf "Warning: external solver not set~n")
    '?))

(define-parameter lite? : Boolean #f)

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

(: es⊢e : (℘ -e) -s → -R)
(define (es⊢e φs e)

  (when (∋ φs -ff)
    ;; Rule `{… #f …} ⊢ e : ✓` is not always desirable, because
    ;; sometimes we want `{… #f …} ⊢ (¬ e) : ✓`, which means `{… #f …} ⊢ e : ✗`
    ;; This is a problem with precision rather than soundness, but I want
    ;; (obviously) inconsistent path-conditions to not exist in the first place.
    (error 'es⊢e "Attempt to prove/refute with inconsistent path-condition"))

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
         (if (lite?) '? ((es⊢ₑₓₜe) φs e)))]
       [else '?]))
    (printf "~a ⊢ ~a : ~a~n" (set-map φs show-e) (show-s e) ans)))

(define (Γ⊢e [Γ : -Γ] [e : -s]) (es⊢e (-Γ-facts Γ) e))
(define (plausible-es-s? [φs : (℘ -e)] [s : -s]) (not (eq? '✗ (es⊢e φs s))))

(: plausible-W? : (℘ -e) (Listof -V) -s → Boolean)
;; Check if value(s) `Vs` can instantiate symbol `s` given path condition `φs`
;; - #f indicates a definitely bogus case
;; - #t indicates (conservative) plausibility
(define (plausible-W? φs Vs s)
  (match* (Vs s)
    [(_ (-@ 'values es _))
     (and (= (length Vs) (length es))
          (for/and : Boolean ([V Vs] [e es])
            (plausible-V-s? φs V e)))]
    [((list V) _) #:when s
     (plausible-V-s? φs V s)]
    [(_ (or (? -v?) (-@ (? -prim?) _ _))) #f] ; length(Vs) ≠ 1, length(s) = 1
    [(_ #f) #t]))

(: plausible-V-s? : (℘ -e) -V -s → Boolean)
(define (plausible-V-s? φs V s)
  (define-syntax-rule (with-prim-checks p? ...)
    (cond
      [s
       (match V
         ['undefined ; (ugly) This needs to come before (? -o?)
          (cond
            [(-v? s) #f]
            [else
             (case (es⊢e φs (-?@ 'defined? s))
               [(✗ ?) #t]
               [(✓)   #f])])]
         [(or (-St si _) (-St* si _ _ _)) #:when si
          (plausible-es-s? φs (-?@ (-st-p si) s))]
         [(or (? -Vector?) (? -Vector/hetero?) (? -Vector/homo?))
          (plausible-es-s? φs (-?@ 'vector? s))]
         [(or (? -Clo?) (? -Ar?) (? -o?))
          (plausible-es-s? φs (-?@ 'procedure? s))]
         [(-b (? p?))
          (and (plausible-es-s? φs (-?@ 'p? s))
               (implies (-b? s) (equal? V s)))] ...
         [(or (? -=>_?) (? -St/C?) (? -x/C?))
          (for/and : Boolean ([p : -o '(procedure? p? ...)])
            (case (es⊢e φs (-?@ p s))
              [(✓)   #f]
              [(✗ ?) #t]))]
         [(-● ps)
          (define φs* (for*/set: : (℘ -e) ([p ps] [s (in-value (-?@ p s))] #:when s) s))
          (and (es⊓ φs φs*) #t)]
         [_ #t])]
      [else #t]))
  
  ;; order matters for precision, in the presence of subtypes
  (with-debugging/off ((ans) (with-prim-checks integer? real? number? string? symbol? keyword? not boolean?))
    (printf "plausible-V-s: ~a ⊢ ~a : ~a -> ~a~n" (set-map φs show-e) (show-V V) (show-s s) ans)))

(: es⊓ : (℘ -e) (℘ -e) → (Option (℘ -e)))
(define (es⊓ es₀ es₁)
  (with-debugging/off
    ((ans)
     (for/fold ([es₀ : (Option (℘ -e)) es₀]) ([e₁ es₁])
       (and es₀
            (case (es⊢e es₀ e₁)
              [(✓ ?) (set-add es₀ e₁)]
              [(✗)   #f]))))
    (printf "es⊓:~n")
    (printf "  - ~a~n" (set-map es₀ show-e))
    (printf "  - ~a~n" (set-map es₁ show-e))
    (printf "  --> ~a~n~n" (and ans (set-map ans show-e)))))

(: Γ⊓ : -Γ -Γ → (Option -Γ))
;; Join 2 path conditions, eliminating obvious inconsistencies
(define (Γ⊓ Γ₀ Γ₁)
  (match-define (-Γ φs₀ as₀ γs₀) Γ₀)
  (match-define (-Γ φs₁ _   γs₁) Γ₁)
  (cond
    [(es⊓ φs₀ φs₁) =>
     (λ ([φs₀* : (℘ -e)]) (-Γ φs₀* as₀ (∪ γs₀ γs₁)))]
    [else #f]))

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
    [(-● ps)
     (or (for*/or : (U #f '✓ '✗) ([p ps])
           (case (p⇒p p 'not)
             [(✓) '✗]
             [(✗) '✓]
             [(?) #f]))
         '?)]
    [_ '✓]))

(: p∋Vs : -V -V * → -R)
;; Check if value satisfies predicate
(define (p∋Vs p . Vs)
  
  (define (check-proc-arity-1 [V : -V]) : -R
    (match (p∋Vs 'procedure? V)
      ['✓ (decide-R (arity-includes? (assert (V-arity V)) 1))]
      [ans ans]))

  (match Vs
    [(list (-● ps)) #:when (-o? p)
     (or (for/or : (U #f '✓ '✗) ([q ps])
           (case (p⇒p q p)
             [(✓) '✓]
             [(✗) '✗]
             [(?) #f]))
         '?)]
    [_
     (match p
       [(? -st-mk?) '✓]
       [(? -st-mut?) '✓]
       [(? -st-ac?) '✓]
       [(-st-p si)
        (match Vs
          [(list (or (-St sj _) (-St* sj _ _ _)))
           ;; TODO: no sub-struct for now. May change later.
           (decide-R (equal? si (assert sj)))]
          [(list (-● _)) '?]
          [_ '✗])]
       [(? symbol?)
        (case p
          ;; Insert manual rules here
          [(procedure?)
           (match Vs
             [(list (-● _)) '?]
             [(list (or (? -o?) (? -Clo?) (? -Ar?) (? -Not/C?))) '✓]
             [(list (or (-And/C flat? _ _) (-Or/C flat? _ _) (-St/C flat? _ _))) (decide-R flat?)]
             [_ '✗])]
          [(vector?)
           (match Vs
             [(list (-● _)) '?]
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
       [_ '?])]))

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

(: φs/ensure-consistency : (HashTable -e -e) (℘ -e) → (Option (℘ -e)))
;; Substitute and throw away inconsistent path-condition
(define (φs/ensure-consistency m φs)
  (define subst (e/map m))
  (define-values (acc φs*)
    (for/fold ([acc : (Option (℘ -e)) φs]
               [φs* : (℘ -e) ∅])
              ([φ φs])
      (cond
        [acc
         (define φ* (subst φ))
         (if (and (not (equal? φ* φ)) (eq? '✗ (es⊢e acc φ*)))
             (values #f ∅)
             (values (set-add acc φ*) (set-add φs* φ*)))]
        [else (values #f ∅)])))
  (and acc φs*))

(: Γ/ensure-consistency : (HashTable -e -e) -Γ → (Option -Γ))
;; Substitute free occurrences of `x` with `e` in path condition  
;; Throw away inconsistent path-condition
(define (Γ/ensure-consistency m Γ)
  (with-debugging/off
    ((Γₐ)
     (match-define (-Γ φs as γs) Γ)
     (define φs* (φs/ensure-consistency m φs))
     (cond
       [φs*
        (define as*
          (let ([subst (e/map m)])
            (for/hash : (HashTable Var-Name -e) ([(x e) as])
              (values x (subst e)))))
        (define γs* (map/set (γ/ m) γs))
        (-Γ φs* as* γs*)]
       [else #f]))
    (parameterize ([verbose? #t])
      (printf "Γ/: ~a~n"
              (for/list : (Listof Sexp) ([(x y) m])
                `(,(show-e x) ↦ ,(show-e y))))
      (printf "  - from: ~a~n" (show-Γ Γ))
      (printf "  - to  : ~a~n" (show-Γ Γₐ))
      (printf "~n"))))


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
  (check-✓ (es⊢e ∅ 'not))
  (check-✓ (es⊢e ∅ (-b 0)))
  (check-✗ (es⊢e ∅ (-b #f)))
  (check-? (es⊢e ∅ (-x 'x)))
  (check-✗ (es⊢e ∅ (-?@ 'not (-b 0))))
  (check-✓ (es⊢e ∅ (-?@ 'equal? (-x 'x) (-x 'x))))
  (check-✓ (es⊢e ∅ (-?@ '+ (-x 'x) (-x 'y))))
  (check-✗ (es⊢e ∅ (-?@ -cons? -null)))
  (check-✗ (es⊢e ∅ (-?@ 'null? (-?@ -cons (-b 0) (-b 1)))))
  
  ;; Γ ⊢ e
  (check-✓ (es⊢e {set (assert (-?@ -cons? (-x 'x)))} (-x 'x)))
  (check-✓ (es⊢e {set (assert (-?@ 'integer? (-x 'x)))} (-?@ 'real? (-x 'x))))
  (check-✓ (es⊢e {set (assert (-?@ 'not (-?@ 'number? (-x 'x))))} (-?@ 'not (-?@ 'integer? (-x 'x)))))
  (check-✗ (es⊢e {set (assert (-?@ 'not (-x 'x)))} (-x 'x)))
  (check-? (es⊢e {set (assert (-?@ 'number? (-x 'x)))} (-?@ 'integer? (-x 'x))))

  ;; plausibility
  (check-false (plausible-W? ∅ (list (-b 1)) (-b 2)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (-b 3)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (-?@ 'values (-b 1) (-b 3))))
  (check-false (plausible-W? ∅ (list -tt) -ff))
  (check-true  (plausible-W? ∅ (list -tt) -tt))
  (check-false (plausible-W? {set (assert (-not (-x 'x)))} (list (-b 0)) (-x 'x)))
  )
