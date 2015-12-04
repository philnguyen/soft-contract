#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/function racket/bool
 "untyped-utils.rkt" "utils.rkt" "ast.rkt" "runtime.rkt" "prim-gen.rkt"
 ; for generated code
 (except-in racket/contract -> ->*)
 math/base racket/generator racket/stream racket/string
 racket/extflonum racket/fixnum racket/flonum
 (for-syntax
  racket/base racket/match racket/pretty racket/list racket/set racket/function
  racket/syntax racket/contract syntax/parse
  "untyped-utils.rkt" "utils.rkt" (only-in "prims.rkt" prims ctc? arr? base?) "prim-gen.rkt"))
(require/typed "prims.rkt"
  [base? (Any → Boolean)])
(provide Γ⊢ₑₓₜ MσΓ⊢V∈C MσΓ⊢oW MσΓ⊢e Γ⊢e p∋Vs V≡
         MσΓ⊓ Γ+/-W Γ+/-W∋Ws Γ+/-e spurious?
         
         ;; debugging
         MσΓ⊢₁e)

;; External solver to be plugged in.
;; Return trivial answer by default.
(define Γ⊢ₑₓₜ : (Parameterof (-Γ -e → -R))
  (make-parameter (λ (Γ e) (log-warning "external solver not set") '?)))

(: MσΓ⊢V∈C : -M -σ -Γ -WV -WV → -R)
;; Check if value satisfies (flat) contract
(define (MσΓ⊢V∈C M σ Γ W_v W_c)
  (match-define (-W V e_v) W_v)
  (match-define (-W C e_c) W_c)
  (first-R (V∋Vs C V) (MσΓ⊢e M σ Γ (-?@ e_c e_v))))

(: MσΓ⊢oW : -M -σ -Γ -o -WV * → -R)
;; Check if value `W` satisfies predicate `p`
(define (MσΓ⊢oW M σ Γ p . Ws)
  (define-values (Vs es)
    (for/lists ([Vs : (Listof -V)] [e : (Listof -?e)])
               ([W Ws])
      (values (-W-x W) (-W-e W))))
  (first-R (apply p∋Vs p Vs)
           (MσΓ⊢e M σ Γ (apply -?@ p es))))

(: MσΓ⊢e : -M -σ -Γ -?e → -R)
;; Check if `e` evals to truth if all in `Γ` do
(define (MσΓ⊢e M σ Γ e)
  (cond
    [e
     (define e* (canonicalize Γ e))
     (first-R (MσΓ⊢₁e M σ Γ e*) ((Γ⊢ₑₓₜ) Γ e*))]
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
  (first-R (go 2 Γ) (go-rec 2 Γ e)))

(: MσΓ⊓e : -M -σ -Γ -?e → (Option -Γ))
;; More powerful version of `Γ⊓` that uses global tables
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
;;   return #f --> don't know (conservative answer)
(define (spurious? M σ Γ W)

  (: spurious*? : -?e -V → Boolean)
  (define (spurious*? e V)
    (define-syntax-rule (with-prim-checks p? ...)
      (cond
        [e
         (match V
           [(or (-St s _) (-St/checked s _ _ _))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ (-st-p (assert s)) e)))]
           [(or (? -Vector?) (? -Vector/checked?))
            (equal? 'X (MσΓ⊢e M σ Γ (-?@ 'vector? e)))]
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
           [(-●)
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
  (define proved (first-R (⊢V V) (MσΓ⊢e M σ Γ e)))
  (values (if (equal? 'X proved) #f (Γ+ Γ e))
          (if (equal? '✓ proved) #f (Γ+ Γ (-not e)))))

(: Γ+/-W∋Ws : -M -σ -Γ -WV -WV * → (Values (Option -Γ) (Option -Γ)))
;; Join the environment with `P(V…)` and `¬P(V…)`
(define (Γ+/-W∋Ws M σ Γ W_P . W_Vs)
  (match-define (-W P e_p) W_P)
  (define-values (Vs e_vs)
    (for/lists ([Vs : (Listof -V)] [e_vs : (Listof -?e)])
               ([W W_Vs])
      (values (-W-x W) (-W-e W))))
  (define ψ (apply -?@ e_p e_vs))
  (define proved (first-R (apply V∋Vs P Vs) (MσΓ⊢e M σ Γ ψ)))
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
  (match p
    [(? -st-mk?) '✓]
    [(? -st-mut?) '✓]
    [(? -st-ac?) '✓]
    [(-st-p si)
     (match Vs
       [(list (or (-St sj _) (-St/checked sj _ _ _)))
        ;; TODO: no sub-struct for now. May change later.
        (decide-R (equal? si (assert sj)))]
       [(-●) '?]
       [_ 'X])]
    [(? symbol?)
     (case p
       ;; Insert manual rules here
       [(procedure?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -o?) (? -Clo?) (? -Clo*?) (? -Ar?) (? -Not/C?))) '✓]
          [(list (-And/C flat? _ _) (-Or/C flat? _ _) (-St/C flat? _ _)) (decide-R flat?)]
          [_ 'X])]
       [(vector?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -Vector?) (? -Vector/checked?))) '✓]
          [_ 'X])]
       [(contract?)
        (match Vs
          [(list (-●)) '?]
          [(list (or (? -And/C?) (? -Or/C?) (? -Not/C?) (? -St/C?)
                     (? -Vectorof?) (? -Vector/C?) (? -=>i?)))
           '✓]
          [(list (-Ar (list _) _ _ _ _ _ _ _)) '✓]
          [(list (or (? -st-p?) (-st-mk (-struct-info _ 1 _)) (? -st-ac?))) '✓]
          [(list (? o-arity-includes-1?)) '✓]
          [(list V) '?]
          [_ '?])]
       [(flat-contract?)
        (match Vs
          [(list (-●)) '?]
          [(list (-And/C flat? _ _) (-Or/C flat? _ _)  (-St/C flat? _ _)) (decide-R flat?)]
          [(list (? -Not/C?)) '✓]
          [(list (-Clo (list _) _ _ _) (-Clo* (list _) _ _)) '✓]
          [(list (or (? -Vectorof?) (? -Vector/C?) (? -=>i?))) 'X]
          [(list (-Ar (list _) _ _ _ _ _ _ _)) '✓]
          [(list (or (? -st-p?) (-st-mk (-struct-info _ 1 _)) (? -st-ac?))) '✓]
          [(list (? o-arity-includes-1?)) '✓]
          [_ '?])]
       [(any/c) '✓]
       [(none/c) 'X]
       [(arity-includes?)
        (match Vs
          [(list V_f V_n)
           (cond
             [(-procedure-arity V_f) =>
              (λ ([a : -Arity])
                (match V_n
                  [(-b (? exact-integer? n)) (decide-R (-arity-includes? a n))]
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: invert-e : -M -σ -id (Listof -e) → (Setof -Res))
;; Given proposition `(p? v)`, generate an overapproximation of expressions
;; that could have evaluated to it
(define (invert-e M σ f args)
  (define ans
    (match f
    [(-id-local o 'Λ)
     {set (-Res (apply -?@ o args) ∅)}]
    [_
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
       [_ -Res⊤])]))
  ;(printf "insert-e: ~a ~a ↦ ~a~n" f (map show-e args) (map show-Res (set->list ans)))
  ans)

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
    (define ans
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
    ;(printf "go: ~a ↦ ~a~n" e (and ans (map show-Res (set->list ans))))
    ans)

  (: go* : (Listof -e) → (Option (Setof (Pairof (Listof -e) -es))))
  (define (go* es)
    (define ans
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
    ;(printf "go*: ~a ↦ ~a~n" es ans)
    ans)

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

(module+ test
  (require typed/rackunit)
  
  (define-syntax-rule (check-✓ e) (check-equal? e '✓))
  (define-syntax-rule (check-X e) (check-equal? e 'X))
  (define-syntax-rule (check-? e) (check-equal? e '?))

  ;; V ∈ p
  (check-✓ (p∋Vs 'not (-b #f)))
  (check-✓ (p∋Vs 'boolean? (-b #f)))
  (check-✓ (p∋Vs 'integer? (-b 1)))
  (check-✓ (p∋Vs 'real? (-b 1)))
  (check-✓ (p∋Vs 'number? (-b 1)))
  (check-✓ (p∋Vs 'procedure? (-Clo '(x) (-b 1) -ρ⊥ -Γ⊤)))
  (check-✓ (p∋Vs 'procedure? 'procedure?))
  (check-✓ (p∋Vs -cons? (-St -s-cons (list (-α.tmp (-b 1)) (-α.tmp (-b 2))))))
  (check-X (p∋Vs 'number? (-St -s-cons (list (-α.tmp (-b 1)) (-α.tmp (-b 2))))))
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
                (-?@ 'integer? (-x 'x))))

  ;; MσΓ⊢e for recursive properties
  (define -app (-ref (-id-local 'app '†) '† 0))
  (define -app-body (-b 'app-body))
  (define -len (-ref (-id-local 'len '†) '† 0))
  (define -len-body (-b 'len-body))
  (define -map (-ref (-id-local 'map '†) '† 0))
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
      (⊔ -σ⊥ (-α.def (-id-local 'app '†)) (-Clo '(l₁ l₂) -app-body -ρ⊥ -Γ⊤))
      (-α.def (-id-local 'len '†)) (-Clo '(l) -len-body -ρ⊥ -Γ⊤))
     (-α.def (-id-local 'map '†)) (-Clo '(f xs) -map-body -ρ⊥ -Γ⊤)))
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

  ;(check-equal? (MσΓ⊢e Mdb σdb -Γ⊤ e-len-app) '✓)
  ;(check-equal? (MσΓ⊢e Mdb σdb -Γ⊤ e-len-map) '✓)
)
