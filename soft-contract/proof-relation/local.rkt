#lang typed/racket/base

(provide Γ⊢e ⊢V V∋Vs p∋Vs V≡ p⇒p Γ⊓ Γ⊓e)

(require
 racket/match racket/set
 "../utils/set.rkt" "../utils/debug.rkt" "../utils/untyped-macros.rkt"
 "../primitives/utils.rkt"
 "../ast/definition.rkt"
 "../runtime/path-inv.rkt" "../runtime/simp.rkt" "../runtime/val.rkt" "../runtime/arity.rkt"
 "result.rkt"
 (for-syntax
  racket/base racket/contract
  "../utils/pretty.rkt" 
  "../primitives/utils.rkt"))

;; Syntax generation for checking whether argument satisfies predicate
(begin-for-syntax

  ;; Inspect inner application to see if it satisfies predicate
  (define/contract (generate-app-clauses p zs)
    (identifier? identifier? . -> . (listof syntax?))
    (define ⊢e (datum->syntax zs '⊢e))
    (define p⇒p (datum->syntax zs 'p⇒p))
    (define -Λ (datum->syntax zs '-Λ))

    (for/list ([(o o-rng) prim-ranges])

      ;; Default case: application's range matches predicate exactly
      (define main-clause #`[(#,o-rng) '✓])
      
      ;; Refined cases: predicate is more refined than application's coarsest range
      (define/contract refined-clauses (listof syntax?)
        (for/list ([(o-rng* o-doms) (hash-ref prim-refinements-for-ranges o (hasheq))])
          
          (define/contract args (listof identifier?)
            (for/list ([(_ i) (in-indexed o-doms)])
              (datum->syntax #f (string->symbol (format "x~a" (n-sub i))))))
          
          (define/contract preconds (listof syntax?)
            (for/list ([dom o-doms] [arg args])
              #`(eq? '✓ (#,⊢e (-@ '#,dom (list #,arg) #,-Λ)))))
          
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

(: Γ⊢e : -Γ -?e → -R)
;; Check if `e` evals to truth given `M`
(define (Γ⊢e Γ e)

  (: ⊢e : -e → -R)
  ;; Check if expression returns truth
  (define (⊢e e)
    (match e
      [(-b b) (if b '✓ 'X)]
      [(? -•?) '?]
      [(? -v?) '✓]
      [x #:when (Γ-has? Γ x) '✓]
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
                  [(and (-st-mk? o) (base? p)) 'X]
                  [else '?])])]
            [_ '?]))
      ;(printf "generated:~n~a~n" (syntax->datum ans))
      ans)

    (match p
      [(? -st-mk?) '✓]
      [(-st-p si)
       (match xs
         [(list (-@ (-st-mk sj) _ _)) ; TODO: No sub-struct for now.
          (decide-R (equal? si sj))]
         [(list (-b _)) 'X]
         [(list (-@ (? symbol? f) _ _))
          (cond ;; HACK for now
            [(hash-ref prim-ranges f #f)
             =>
             (λ ([f-rng : Symbol])
               (cond
                 [(∋ (set 'integer? 'real? 'number? 'vector? 'boolean? 'not 'null?) f-rng) 'X]
                 [else '?]))]
            [else '?])]
         [_ '?])]
      ['not (not-R (⊢e (car xs)))] ; assume right arity
      ['any/c '✓]
      ['none/c 'X]
      ['equal?
       (match xs
         [(list e₁ e₂)
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
           [((-@ (? -o? p) (list e) _) (-@ (? -o? q) (list e) _))
            (p⇒p p q)] ; FIXME
           [((-@ (? -o? p) (list e) _) e)
            (cond
              [(eq? 'not p) 'X]
              [(and (symbol? p) (boolean-excludes? p)) '✓]
              [(-st-p? p) '✓]
              [else '?])]
           [((-@ (or '= 'equal?) (list e₁ e₂) _) (-@ (? -o? p) (list e₁) _))
            (⊢@ p (list e₂))]
           [((-@ (or '= 'equal?) (list e₁ e₂) _) (-@ (? -o? p) (list e₂) _))
            (⊢@ p (list e₁))]
           [(_ _) '?])]
        [(_ R) R]))
    (dbg 'e⊢e "~a ⊢ ~a : ~a~n~n" (show-e e₁) (show-e e₂) ans)
    ans)

  (define ans
    (cond
      [e
       (first-R (⊢e e)
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
    [(-●) '?]
    [_ '✓]))

(: V∋Vs : -V -V * → -R)
;; Check if value satisfies predicate
(define (V∋Vs P . Vs)
  (cond
    [(-o? P) (apply p∋Vs P Vs)] ; FIXME
    [else
     (match P
       [(-Clo `(,x) (-b #f) _ _) 'X]
       [(-Clo `(,x) (? -v? v) _ _) (if (-•? v) '? '✓)]
       [(-Clo `(,x) (-x x) _ _) (⊢V (car Vs))] ; |Vs| = 1 guaranteed
       [_ '?])]))

(: p∋Vs : -o -V * → -R)
;; Check if value satisfies predicate
(define (p∋Vs p . Vs)
  
  (define (check-proc-arity-1 [V : -V]) : -R
    (match (p∋Vs 'procedure? V)
      ['✓ (decide-R (arity-includes? (assert (-procedure-arity V)) 1))]
      [ans ans]))

  (match p
    [(? -st-mk?) '✓]
    [(? -st-mut?) '✓]
    [(? -st-ac?) '✓]
    [(-st-p si)
     (match Vs
       [(list (or (-St sj _) (-St/checked sj _ _ _)))
        ;; TODO: no sub-struct for now. May change later.
        (decide-R (equal? si (assert sj)))]
       [(list (-●)) '?]
       [_ 'X])]
    [(? symbol?)
     (case p
       ;; Insert manual rules here
       [(procedure?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -o?) (? -Clo?) (? -Clo*?) (? -Ar?) (? -Not/C?))) '✓]
          [(list (or (-And/C flat? _ _) (-Or/C flat? _ _) (-St/C flat? _ _))) (decide-R flat?)]
          [_ 'X])]
       [(vector?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -Vector?) (? -Vector/checked?) (? -Vector/same?))) '✓]
          [_ 'X])]
       [(contract?)
        (match Vs
          [(list (or (? -=>i?) (? -And/C?) (? -Or/C?) (? -Not/C?)
                     (? -Vectorof?) (? -Vector/C?) (? -St/C?) (? -x/C?))) '✓]
          [(list V) (check-proc-arity-1 V)]
          [_ '?])]
       [(flat-contract?)
        (match Vs
          [(list V) (check-proc-arity-1 V)]
          [_ '?])]
       [(any/c) '✓]
       [(none/c) 'X]
       [(arity-includes?)
        (match Vs
          [(list V_f V_n)
           (cond
             [(-procedure-arity V_f) =>
              (λ ([a : Arity])
                (match V_n
                  [(-b (? simple-arity? n)) (decide-R (arity-includes? a n))]
                  [_ '?]))]
             [else '?])])]
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
                      [_ (cond [(and (base? p) (and (match? Vs (list (not (? -b?)))))) 'X]
                               [else '?])])]))]
          [else '?])])]))

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
    [(_ 'none/c) 'X]
    [((? symbol? p) (? symbol? q))
     (cond [(∋ (hash-ref implications p →∅) q) '✓]
           [(∋ (hash-ref exclusions p →∅) q) 'X]
           [else '?])]
    [((-st-p si) (-st-p sj))
     ;; TODO: no sub-struct for now. Probably changes later
     (decide-R (equal? si sj))]
    [(_ _)
     (cond [(or (and (symbol? p) (hash-has-key? implications p) (-st-p? q))
                (and (symbol? q) (hash-has-key? implications q) (-st-p? p)))
            'X]
           [else '?])]))

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


(module+ test
  (require "../ast/definition.rkt"
           "../runtime/env.rkt" "../runtime/path-inv.rkt" "../runtime/addr.rkt"
           "for-test.rkt")
  
  ;; V ∈ p
  (check-✓ (p∋Vs 'not (-b #f)))
  (check-✓ (p∋Vs 'boolean? (-b #f)))
  (check-✓ (p∋Vs 'integer? (-b 1)))
  (check-✓ (p∋Vs 'real? (-b 1)))
  (check-✓ (p∋Vs 'number? (-b 1)))
  (check-✓ (p∋Vs 'procedure? (-Clo '(x) (-b 1) -ρ⊥ -Γ⊤)))
  (check-✓ (p∋Vs 'procedure? 'procedure?))
  (check-✓ (p∋Vs -cons? (-St -s-cons (list (-α.fld -tt) (-α.fld -ff)))))
  (check-X (p∋Vs 'number? (-St -s-cons (list (-α.fld -ff) (-α.fld -tt)))))
  (check-X (p∋Vs 'integer? (-b 1.5)))
  (check-X (p∋Vs 'real? (-b 1+1i)))
  (check-? (p∋Vs 'integer? -●/V))

  ;; ⊢ e
  (check-✓ (Γ⊢e -Γ⊤ 'not))
  (check-✓ (Γ⊢e -Γ⊤ (-b 0)))
  (check-X (Γ⊢e -Γ⊤ (-b #f)))
  (check-? (Γ⊢e -Γ⊤ (-x 'x)))
  (check-X (Γ⊢e -Γ⊤ (-?@ 'not (-b 0))))
  (check-✓ (Γ⊢e -Γ⊤ (-?@ 'equal? (-x 'x) (-x 'x))))
  (check-✓ (Γ⊢e -Γ⊤ (-?@ '+ (-x 'x) (-x 'y))))
  (check-X (Γ⊢e -Γ⊤ (-?@ -cons? -null)))
  (check-X (Γ⊢e -Γ⊤ (-?@ 'null? (-?@ -cons (-b 0) (-b 1)))))
  
  ;; Γ ⊢ e
  (check-✓ (Γ⊢e (Γ+ -Γ⊤ (-?@ -cons? (-x 'x))) (-x 'x)))
  (check-✓ (Γ⊢e (Γ+ -Γ⊤ (-?@ 'integer? (-x 'x))) (-?@ 'real? (-x 'x))))
  (check-✓ (Γ⊢e (Γ+ -Γ⊤ (-?@ 'not (-?@ 'number? (-x 'x))))
                (-?@ 'not (-?@ 'integer? (-x 'x)))))
  (check-X (Γ⊢e (Γ+ -Γ⊤ (-?@ 'not (-x 'x))) (-x 'x)))
  (check-? (Γ⊢e (Γ+ -Γ⊤ (-?@ 'number? (-x 'x)))
                (-?@ 'integer? (-x 'x)))))
