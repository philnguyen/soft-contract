#lang typed/racket/base

(provide Γ⊢ₑₓₜ Γ⊢e partition-Γs ⊢V p∋Vs V≡ p⇒p Γ⊓ Γ⊓e most-specific-pred)

(require
 racket/match racket/set
 "../utils/main.rkt"
 "../primitives/utils.rkt"
 "../ast/definition.rkt"
 "../runtime/main.rkt"
 "result.rkt"
 (for-syntax
  racket/base racket/contract
  "../utils/pretty.rkt" 
  "../primitives/utils.rkt"))

;; External solver to be plugged in.
;; Return trivial answer by default.
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

  (match-define (-Γ facts _ _) Γ)

  (: ⊢e : -e → -R)
  ;; Check if expression returns truth
  (define (⊢e e)
    (match e
      [(-b b) (if b '✓ '✗)]
      [(? -•?) '?]
      [(? -v?) '✓]
      [x #:when (∋ facts x) '✓]
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
    (define ans
      (match* ((⊢e e₁) (⊢e e₂))
        [('✗ _) '✓]
        [(_ '?)
         (match* (e₁ e₂)
           ; e ⇒ e
           [(e e) '✓]
           ; NOTE: Don't abuse "contrapositive"
           ; (¬e₁ ⊢ ¬e₂ : ✗) does not follow from (e₂ ⊢ e₁ : ✗)
           [((-not e₁*) (-not e₂*))
            (if (equal? '✓ (e⊢e e₂* e₁*)) '✓ '?)]
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
    ;(dbg 'e⊢e "~a ⊢ ~a : ~a~n~n" (show-e e₁) (show-e e₂) ans)
    ans)

  (define ans
    (cond
      [e
       (first-R
        (⊢e e)
        (for*/fold ([R : -R '?])
                   ([e₀ facts] #:when (equal? '? R)
                    [R* (in-value (e⊢e e₀ e))])
          R*)
        ((Γ⊢ₑₓₜ) Γ e))]
      [else '?]))
  ;(dbg '⊢ "~a ⊢ ~a : ~a~n~n"(show-Γ Γ) (show-s e) ans)
  ans)

(: partition-Γs : (℘ -Γ) -s → (Values (℘ -Γ) (℘ -Γ) (℘ -Γ)))
;; Given a set of path-conditions, partition them into those that
;; proves, refute, and ambig the proposition, respectively
(define (partition-Γs Γs s)
  (define-set ✓Γ : -Γ)
  (define-set ✗Γ : -Γ)
  (define-set ?Γ : -Γ)
  (for ([Γ Γs])
    (case (Γ⊢e Γ s)
      [(✓) (✓Γ-add! Γ)]
      [(✗) (✗Γ-add! Γ)]
      [(?) (?Γ-add! Γ)]))
  (values ✓Γ ✗Γ ?Γ))

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

(: Γ⊓ : -Γ -Γ → (Option -Γ))
;; Join path invariants. Return `#f` to represent the bogus environment (⊥)
(define (Γ⊓ Γ Γ*)
  (for/fold ([Γ : (Option -Γ) Γ]) ([φ (-Γ-facts Γ*)])
    (and Γ (Γ⊓e Γ φ))))

(: Γ⊓e : -Γ -s → (Option -Γ))
;; Refine path invariant with expression.
;; Note: `∅` is `⊤` (no assumption), `#f` is `⊥` (spurious, anything is true).
;; The operation doesn't guarantee absolute precision.
;; In general, it returns an upperbound of the right answer.
(define (Γ⊓e Γ e)
  (if (equal? '✗ (Γ⊢e Γ e)) #f (Γ+ Γ e)))

(: most-specific-pred : -Γ -e → -o)
;; Return the most specific predicate in path-invariant describing given expression
(define (most-specific-pred Γ e)
  (for/fold ([best : -o 'any/c]) ([φ (-Γ-facts Γ)])
    (match φ
      [(-@ (? -o? o) (list (== e)) _) #:when (equal? '✓ (p⇒p o best))
       o]
      [(or (== e) (-not (-not (== e)))) #:when (and e (equal? '✓ (p⇒p 'values best)))
       'values]
      [_ best])))


(module+ test
  (require "../ast/definition.rkt" "../runtime/main.rkt" "for-test.rkt")
  
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
                (-?@ 'integer? (-x 'x)))))
