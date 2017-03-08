#lang typed/racket/base

(provide Γ⊢e φs⊢e ⊢V p∋Vs p⇒p ps⇒p
         plausible-φs-s? plausible-W? plausible-V-s?
         first-R
         sat-one-of
         (all-from-out "result.rkt" "base-assumptions.rkt"))

(require (for-syntax racket/base
                     racket/contract
                     "../utils/pretty.rkt")
         racket/match
         racket/set
         racket/bool
         syntax/parse/define
         (only-in racket/list first second)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "base-assumptions.rkt"
         "result.rkt"
         )

;; Check whether predicate excludes boolean
(define boolean-excludes? (set->predicate (get-exclusions 'boolean?)))

(: ⊢e : -e → -R)
;; Check if expression returns truth
(define (⊢e e)
  (match e
    [(-b b) (if b '✓ '✗)]
    [(? -•?) '?]
    [(? -v?) '✓]
    [(-@ f xs _) (⊢@ f xs)]
    [_ '?]))

(: ⊢@ : -e (Listof -e) → -R)
  ;; Check if application returns truth
(define (⊢@ p xs)

  (match p
    [(? -st-mk?) '✓]
    [(-st-p si)
     (match xs
       [(list (-@ (-st-mk sj) _ _)) ; TODO: No sub-struct for now.
        (boolean->R (equal? si sj))]
       [(list (-b _)) '✗]
       [(list (-@ (? symbol? f) _ _))
        (cond ;; HACK for now
          [(∋ (seteq 'integer? 'real? 'number? 'vector? 'boolean? 'not 'null?)
              (get-conservative-range f))
           '✗]
          [else '?])]
       [_ '?])]
    ['not (not-R (⊢e (car xs)))] ; assume right arity
    ['any/c '✓]
    ['none/c '✗]
    [(or 'equal? 'eq? '=)
     (match xs
       [(list e₁ e₂)
        (match* (e₁ e₂)
          [((? -λ? v₁) (? -λ? v₂)) ; can't compare higher-order literals
           (if (equal? v₁ v₂) '? '✗)]
          [((? -•?) _) '?]
          [(_ (? -•?)) '?]
          [((? -v? v₁) (? -v? v₂)) (boolean->R (equal? v₁ v₂))]
          [((-x x) (-x y))
           (if (equal? x y) '✓ '?)]
          [((-@ f xs _) (-@ g ys _))
           ; lose precision. Don't need `f = g, x = y` to prove `f(x) = g(y)`
           (cond
             [(and
               (or
                (and (-λ? f) (equal? f g))
                (eq? '✓ (⊢e (-@ 'equal? (list f g) +ℓ₀))))
               (= (length xs) (length ys)))
              (define res
                (for/seteq: : (℘ -R) ([x xs] [y ys])
                  (⊢e (-@ 'equal? (list x y) +ℓ₀))))
              (cond
                [(or (set-empty? res) (equal? res {seteq '✓})) '✓]
                [(and (-st-mk? f) (∋ res '✗)) '✗]
                [else '?])]
             [else '?])]
          [(_ _) (if (equal? e₁ e₂) '✓ '?)])]
       [_ #|TODO|# '?])]
    ['positive?
     (⊢@ '> (list (car xs) (-b 0)))]
    ['negative?
     (⊢@ '< (list (car xs) (-b 0)))]
    [(? symbol?)
     (cond
       [(and (eq? p 'boolean?) (match? xs (list (-@ (? -st-p?) _ _)))) '✓]
       [(and (eq? p 'procedure?) (match? xs (list (or (? -λ?) (? -case-λ?))))) '✓]
       [(boolean-excludes? (get-conservative-range p)) '✓]
       [else '?])]
    [_ '?]))

(: Γ⊢e : -Γ -s → -R)
(define (Γ⊢e Γ s) (φs⊢e (-Γ-facts Γ) s))

(: φs⊢e : (℘ -e) -s → -R)
(define (φs⊢e φs e)

  (when (∋ φs -ff)
    ;; Rule `{… #f …} ⊢ e : ✓` is not always desirable, because
    ;; sometimes we want `{… #f …} ⊢ (¬ e) : ✓`, which means `{… #f …} ⊢ e : ✗`
    ;; This is a problem with precision rather than soundness, but I want
    ;; (obviously) inconsistent path-conditions to not exist in the first place.
    (error 'φs⊢e "Attempt to prove/refute with inconsistent path-condition"))

  (: e⊢e : -e -e → -R)
  ;; Check if `e₂` returns truth when `e₁` does
  (define (e⊢e e₁ e₂)
    (with-debugging/off
      ((ans)
       ;; (⊢e e₂) is not redundant, because this may be just a sub-exp of the original goal
       (case (⊢e e₁)
         [(✗) '✓]
         [else
          (match (⊢e e₂)
            ['?
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
               [((-@ (? -v? p) (list e) _) (-@ (? -v? q) (list e) _))
                (p⇒p p q)] ; FIXME
               [((-@ (? -o? p) (list e) _) e)
                (cond
                  [(eq? 'not p) '✗]
                  [(and (symbol? p) (boolean-excludes? p)) '✓]
                  [(-st-p? p) '✓]
                  [else '?])]
               [((-@ (or '= 'equal? 'eq?) (list e₁ e₂) _) (-@ (? -o? p) (list e₁) _))
                (⊢@ p (list e₂))]
               [((-@ (or '= 'equal? 'eq?) (list e₁ e₂) _) (-@ (? -o? p) (list e₂) _))
                (⊢@ p (list e₁))]
               [((-@ (or '= 'equal? 'eq?) (list e (-b b₁)) _)
                 (-@ (or '= 'equal? 'eq?) (list e (-b b₂)) _))
                (boolean->R (equal? b₁ b₂))]
               [((-@ (or '= 'equal? 'eq?) (list (-b b₁) e) _)
                 (-@ (or '= 'equal? 'eq?) (list (-b b₂) e) _))
                (boolean->R (equal? b₁ b₂))]
               [(_ _) '?])]
            [R R])]))
      (printf "~a ⊢ ~a : ~a~n" (show-e e₁) (show-e e₂) ans)))

  (with-debugging/off
    ((ans)
     (cond
       [e
        (first-R
         (⊢e e)
         (match e
           [_ #:when (∋ φs       e ) '✓]
           [_ #:when (∋ φs (-not e)) '✗]
           [(-not e*) #:when (∋ φs e*) '✗]
           [else '?])
         (for*/fold ([R : -R '?])
                    ([φ (in-set φs)] #:when (eq? '? R))
           (e⊢e φ e))
         '?)]
       [else '?]))
    (printf "~a ⊢ ~a : ~a~n" (set-map φs show-e) (show-s e) ans)))

(define (plausible-φs-s? [φs : (℘ -e)] [s : -s]) : Boolean
  (with-debugging/off
    ((a) (not (eq? '✗ (φs⊢e φs s))))
    (printf "plausible-φs-s: ~a ⊢ ~a : ~a~n"
            (set-map φs show-e)
            (show-s s)
            a)))

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
    [(_ _) #t]))

(: plausible-V-s? : (℘ -e) -V -s → Boolean)
(define (plausible-V-s? φs V s)
  (define-syntax-rule (with-prim-checks p? ...)
    (cond
      [s
       (match V
         [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _)) #:when 𝒾
          (plausible-φs-s? φs (-?@ (-st-p 𝒾) s))]
         [(or (? -Vector?) (? -Vector^?) (? -Vector/guard?))
          (plausible-φs-s? φs (-?@ 'vector? s))]
         [(or (? -Clo?) (? -Case-Clo?) (? -Ar?) (? -o?))
          (plausible-φs-s? φs (-?@ 'procedure? s))]
         [(-b (? p?))
          (and (plausible-φs-s? φs (-?@ 'p? s))
               (plausible-φs-s? φs (-?@ 'equal? s V))
               (implies (-b? s) (equal? V s)))] ...
         #|;; FIXME tmp. hack
         [(-b (and (? number?) (? exact?)))
          (and (plausible-φs-s? φs (-?@ 'exact? s))
               (plausible-φs-s? φs (-?@ 'equal? s V))
               (implies (-b? s) (equal? V s)))]
         [(-b (and (? number?) (? inexact?)))
          (and (plausible-φs-s? φs (-?@ 'inexact? s))
               (plausible-φs-s? φs (-?@ 'equal? s V))
               (implies (-b? s) (equal? V s)))]
         |#
         ;; end tmp. hack
         [(or (? -=>_?) (? -St/C?) (? -x/C?))
          (for/and : Boolean ([p : -o '(procedure? p? ...)])
            (case (φs⊢e φs (-?@ p s))
              [(✓)   #f]
              [(✗ ?) #t]))]
         [(-b (list))
          (plausible-φs-s? φs (-?@ 'null? s))]
         [(? -v? v)
          (plausible-φs-s? φs (-?@ 'equal? s v))]
         [(-● ps)
          (cond
            [(-ar? s) #f]
            [else
             (not (for/or : Boolean ([p ps])
                    (match p
                      [(? -o? o) (equal? '✗ (φs⊢e φs (-@ o (list s) +ℓ₀)))]
                      [(-λ (list x) e) (equal? '✗ (φs⊢e φs (e/ (-x x) s e)))]
                      [_ #f])))])
          ]
         [_ #t])]
      [else #t]))
  
  ;; order matters for precision, in the presence of subtypes
  (with-debugging/off ((ans) (with-prim-checks
                               exact-positive-integer?
                               exact-nonnegative-integer?
                               exact-integer?
                               integer?
                               real?
                               number?
                               null?
                               string?
                               symbol?
                               keyword?
                               not
                               boolean?
                               char?
                               eof-object?))
    (printf "plausible-V-s: ~a ⊢ ~a : ~a -> ~a~n" (set-map φs show-e) (show-V V) (show-s s) ans)))

(: ⊢V : -V → -R)
;; Check if value represents truth
(define ⊢V
  (match-lambda
    [(-b #f) '✗]
    [(-● ps)
     (or (for/or : (U #f '✓ '✗) ([p ps] #:when (-v? p))
           (case (p⇒p p 'not)
             [(✓) '✗]
             [(✗) '✓]
             [(?) #f]))
         '?)]
    [_ '✓]))

(: p∋Vs : -σ (U -v -V) -V * → -R)
;; Check if value satisfies predicate
(define (p∋Vs σ p . Vs)
  
  (define (check-proc-arity-1 [V : -V]) : -R
    (match (p∋Vs σ 'procedure? V)
      ['✓ (boolean->R (arity-includes? (assert (V-arity V)) 1))]
      [ans ans]))

  (with-debugging/off
    ((R) (ann (match Vs
    [(list (-● ps)) #:when (-v? p)
     (ps⇒p ps p)]
    [_
     (match p
       [(? -st-mk?) '✓]
       [(? -st-mut?) '✓]
       [(? -st-ac?) '✓]
       [(-st-p 𝒾)
        (match Vs
          [(list (or (-St 𝒿 _) (-St* (-St/C _ 𝒿 _) _ _)))
           ;; TODO: no sub-struct for now. May change later.
           (boolean->R (equal? 𝒾 (assert 𝒿)))]
          [(list (-● ps))
           (or (for/or : (U '✓ '✗ #f) ([p ps] #:when (-st-p? p))
                 (match-define (-st-p 𝒾*) p)
                 (boolean->R (equal? 𝒾* 𝒾)))
               '?)]
          [_ '✗])]
       [(-Ar _ (app ⟪α⟫->-α (? -o? o)) _) (apply p∋Vs σ o Vs)]
       [(-One-Of/C bs) (sat-one-of (car Vs) bs)]
       [(? symbol?)
        (assert (not (match? Vs (list (? -●?))))) ; just for debugging

        (define-simple-macro (with-base-predicates (o?:id ...) clauses ...)
          (case p
            [(o?)
             (match Vs
               [(list (-b b)) (boolean->R (o? b))]
               [_ '✗])] ...
            clauses ...))

        #;(define-syntax-parser with-base-predicates
          [(_ (o? ...) clauses ...)
           (define special-cases
             (for/list ([o (in-list (syntax->list #'(o? ...)))])
               #`[(p?)
                  (match Vs
                    [(list (-b b)) (boolean->R #,(syntax-parse o
                                                   [[p?:id #:guard g?:id]
                                                    #`(and (g? b) (p? b))]
                                                   [p?:id #`(p? b)]))]
                    [_ '✗])]))
           #`(case p
               #,@special-cases
               clauses ...)])
        
        (with-base-predicates (exact-positive-integer?
                               exact-nonnegative-integer?
                               exact-integer?
                               integer?
                               inexact-real?
                               real?
                               number?
                               #;[exact? #:guard number?]
                               #;[inexact? #:guard number?]
                               null?
                               boolean?
                               path-string?
                               string?
                               char?
                               symbol?
                               void?
                               eof-object?)
          ;; Insert manual rules here
          [(zero?)
           (match Vs
             [(list (-b (? number? n))) (boolean->R (zero? n))]
             [(list (-● _)) '?]
             [_ '✗])]
          [(procedure?)
           (match Vs
             [(list (or (? -o?) (? -Clo?) (? -Case-Clo?) (? -Ar?) (? -Not/C?) (? -One-Of/C?))) '✓]
             [(list (or (-And/C flat? _ _) (-Or/C flat? _ _) (-St/C flat? _ _))) (boolean->R flat?)]
             [_ '✗])]
          [(vector?)
           (match Vs
             [(list (or (? -Vector?) (? -Vector^?) (? -Vector/guard?))) '✓]
             [_ '✗])]
          [(contract?)
           (match Vs
             [(list (or (? -=>_?) (? -And/C?) (? -Or/C?) (? -Not/C?) (? -Not/C?)
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
              (boolean->R (arity-includes? a b))]
             [_ '?])]
          [(immutable?)
           (match Vs
             [(list (-b b)) (boolean->R (immutable? b))]
             ;; always false for now because no support for immutable vectors
             [_ '✗])]
          [(<)
           (match Vs
             [(list (-● ps) (-b (? real? b)))
              (match (set->list ps)
                [(list _ ... (-</c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                [(list _ ... (-≤/c (? real? a)) _ ...) (if (<  a b) '✓ '?)]
                [(list _ ... (->/c (? real? a)) _ ...) (if (>= a b) '✗ '?)]
                [(list _ ... (-≥/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                [(list _ ... (-=/c (? real? a)) _ ...) #:when a (if (<  a b) '✓ '✗)]
                [_ '?])]
             [_ '?])]
          [(<=)
           (match Vs
             [(list (-● ps) (-b (? real? b)))
              (match (set->list ps)
                [(list _ ... (-</c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                [(list _ ... (-≤/c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                [(list _ ... (->/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                [(list _ ... (-≥/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                [(list _ ... (-=/c (? real? a)) _ ...) #:when a (if (<= a b) '✓ '✗)]
                [_ '?])]
             [_ '?])]
          [(>) (p∋Vs σ '< (second Vs) (first Vs))]
          [(>=) (p∋Vs σ '<= (second Vs) (first Vs))]
          [(= equal? eq? char=? string=?)
           (match Vs
             [(list (-b b₁) (-b b₂))   (boolean->R (equal? b₁ b₂))]
             [(list (-● ps) (? -b? b)) (ps⇒p ps (-≡/c b))]
             [(list (? -b? b) (-● ps)) (ps⇒p ps (-≡/c b))]
             [_ '?])]
          [(list?)
           (match Vs
             [(list V)
              (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
              
              (define (combine [Rs : (℘ -R)]) : -R
                (cond [(∋ Rs '?) '?]
                      [(and (∋ Rs '✓) (∋ Rs '✗)) '?]
                      [(∋ Rs '✗) '✗]
                      [else '✓]))

              (define (check-⟪α⟫ [⟪α⟫ : ⟪α⟫]) : -R
                (cond [(seen-has? ⟪α⟫) '✓]
                      [else
                       (seen-add! ⟪α⟫)
                       (combine
                        (for/seteq: : (℘ -R) ([Vᵣ (σ@ σ ⟪α⟫)])
                          (check Vᵣ)))]))
              
              (define (check [V : -V]) : -R
                (match V
                  [(-Cons _ α) (check-⟪α⟫ α)]
                  [(-Cons* α) (check-⟪α⟫ α)]
                  [(-b b) (boolean->R (null? b))]
                  [(-● ps)
                   (cond
                     [(set-empty?
                       (∩ ps {set 'number? 'integer? 'real? 'exact-nonnegative-integer?
                                  'string? 'symbol?}))
                      '?]
                     [else '✗])]
                  [_ '✗]))
              (check V)]
             [_ '✗])]
          ;; Default rules for operations on base values rely on simplification from `-?@`
          [(boolean-excludes? (get-conservative-range p)) '✓]
          [else
           (match Vs
             [(list (? -b? bs) ...)
              (match (apply -?@ p (cast bs (Listof -b)))
                [(-b b) (boolean->R (and b #|force boolean|# #t))]
                [_ '?])]
             [(list (? -●?) ...) '?]
             [_ '?])])]
       [(-not/c (? -v? p))
        (not-R (apply p∋Vs σ p Vs))]
       [(-λ (list x) (-@ 'not (list e) _))
        (not-R (apply p∋Vs σ (-λ (list x) e) Vs))] ; more general than the `not/c` case
       [(-λ (list x) (-@ (? -o? o) (list (-b (? real? a)) (-x x)) _))
        (match Vs
          [(list (-b b))
           (define op : (Real Real → Boolean)
             (case o
               [(<) <]
               [(<=) <=]
               [(>) >]
               [(>=) >=]
               [(=) =]
               [else (error 'p∋Vs "unhandled: ~a" o)]))
           (boolean->R (and (real? b) (op a b)))]
          [(list (-● ps)) #|TODO|# '?]
          [_ '✗])]
       [(-λ (list x) (-@ (? -o? o) (list (-x x) (-b (? real? a))) _))
        (match Vs
          [(list (-b b))
           (define op : (Real Real → Boolean)
             (case o
               [(<) <]
               [(<=) <=]
               [(>) >]
               [(>=) >=]
               [(=) =]
               [else (error 'p∋Vs "unhandled: ~a" o)]))
           (boolean->R (and (real? b) (op b a)))]
          [(list (-● ps)) #|TODO|# '?]
          [_ '✗])]
       [(-≡/c (-b b₁))
        (match-define (list V) Vs)
        (p∋Vs σ 'equal? (-b b₁) V)]
       [_ '?])]) -R))
    (when (equal? p 'equal?)
      (printf "~a ∋ ~a ? : ~a~n" p (map show-V-or-v Vs) R))))

(: V≡ : -V -V → -R)
;; Check if 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (boolean->R (equal? x₁ x₂))]
   [(_ _) '?]))

(: ps⇒p : (℘ -v) -v → -R)
(define (ps⇒p ps p)
  (or (for/or : (U #f '✓ '✗) ([q ps] #:when (-v? q))
        (case (p⇒p q p)
          [(✓) '✓]
          [(✗) '✗]
          [(?) #f]))
      (case p ; special hacky cases where `q` is implied by 2+ predicates
        [(exact-nonnegative-integer?)
         (cond
           [(and (∋ ps 'integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (->/c (? (>/c -1)))
                    (-≥/c (? (>=/c 0)))
                    (-=/c (? (>=/c 0))))))
            '✓]
           [(and (∋ ps 'integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (-</c (? (<=/c 0)))
                    (-≤/c (? (</c  0)))
                    (-=/c (? (</c  0))))))
            '✗]
           [else '?])]
        [(exact-positive-integer?)
         (cond
           [(and (∋ ps 'exact-nonnegative-integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (->/c (? (>=/c 0)))
                    (-≥/c (? (>/c 0)))
                    (-≡/c (-b (? (>/c 0))))
                    (-not/c (-≡/c (-b 0))))))
            '✓]
           [(and (∋ ps 'integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (->/c (? (>=/c 0)))
                    (-≥/c (? (>/c 0)))
                    (-≡/c (-b (? (>/c 0)))))))
            '✓]
           [else '?])]
        [else '?])))

(: p⇒p : -v -v → -R)
;; Return whether predicate `p` definitely implies or excludes `q`.
(define (p⇒p p q)
  (match* (p q)
    [(_ 'any/c) '✓]
    [('none/c _) '✓]
    [(_ 'none/c) '✗]
    [((? symbol? p) (? symbol? q)) (o⇒o p q)]
    [(p 'values)
     (case p
       [(not) '✗]
       [(any/c) '?]
       [else '✓])]
    [((-st-p si) (-st-p sj))
     ;; TODO: no sub-struct for now. Probably changes later
     (boolean->R (equal? si sj))]

    ;; Negate
    [((-not/c (? -v? p)) (-not/c (? -v? q)))
     (case (p⇒p q p)
       [(✓) '✓]
       [else '?])]
    [(p (-not/c (? -v? q)))
     (not-R (p⇒p p q))]
    [((-not/c (? -v? p)) q)
     (case (p⇒p q p)
       [(✓) '✗]
       [else '?])]

    ;; Special rules for reals
    ; 
    [(_ 'positive?) (p⇒p p (->/c 0))]
    [(_ 'negative?) (p⇒p p (-</c 0))]
    [('positive? _) (p⇒p (->/c 0) q)]
    [('negative? _) (p⇒p (-</c 0) q)]
    ; < and <
    [((-</c (? real? a)) (-</c (? real? b))) (if (<= a b) '✓ '?)]
    [((-≤/c (? real? a)) (-≤/c (? real? b))) (if (<= a b) '✓ '?)]
    [((-</c (? real? a)) (-≤/c (? real? b))) (if (<= a b) '✓ '?)]
    [((-≤/c (? real? a)) (-</c (? real? b))) (if (<= a b) '✓ '?)]
    ; > and >
    [((->/c (? real? a)) (->/c (? real? b))) (if (>= a b) '✓ '?)]
    [((-≥/c (? real? a)) (-≥/c (? real? b))) (if (>= a b) '✓ '?)]
    [((->/c (? real? a)) (-≥/c (? real? b))) (if (>= a b) '✓ '?)]
    [((-≥/c (? real? a)) (->/c (? real? b))) (if (>= a b) '✓ '?)]
    ; < and >
    [((-</c (? real? a)) (->/c (? real? b))) (if (<= a b) '✗ '?)]
    [((-≤/c (? real? a)) (-≥/c (? real? b))) (if (<  a b) '✗ '?)]
    [((-</c (? real? a)) (-≥/c (? real? b))) (if (<= a b) '✗ '?)]
    [((-≤/c (? real? a)) (->/c (? real? b))) (if (<= a b) '✗ '?)]
    ; > and <
    [((->/c (? real? a)) (-</c (? real? b))) (if (>= a b) '✗ '?)]
    [((-≥/c (? real? a)) (-≤/c (? real? b))) (if (>  a b) '✗ '?)]
    [((->/c (? real? a)) (-≤/c (? real? b))) (if (>= a b) '✗ '?)]
    [((-≥/c (? real? a)) (-</c (? real? b))) (if (>= a b) '✗ '?)]
    ; <> and 0?
    [((-</c (? real? b)) 'zero?) (if (<= b 0) '✗ '?)]
    [((-≤/c (? real? b)) 'zero?) (if (<  b 0) '✗ '?)]
    [((->/c (? real? b)) 'zero?) (if (>= b 0) '✗ '?)]
    [((-≥/c (? real? b)) 'zero?) (if (>  b 0) '✗ '?)]
    ; exact-nonnegative-integer?
    [('exact-nonnegative-integer? (-</c (? real? r))) (if (<= r 0) '✗ '?)]
    [('exact-nonnegative-integer? (-≤/c (? real? r))) (if (<  r 0) '✗ '?)]
    [('exact-nonnegative-integer? (->/c (? real? r))) (if (<  r 0) '✓ '?)]
    [('exact-nonnegative-integer? (-≥/c (? real? r))) (if (<= r 0) '✓ '?)]
    [((-</c (? real? r)) 'exact-nonnegative-integer?) (if (<= r 0) '✗ '?)]
    [((-≤/c (? real? r)) 'exact-nonnegative-integer?) (if (<  r 0) '✗ '?)]
    ; exact-positive-integer?
    [('exact-positive-integer? (-</c (? real? r))) (if (<  r 1) '✗ '?)]
    [('exact-positive-integer? (-≤/c (? real? r))) (if (<  r 1) '✗ '?)]
    [('exact-positive-integer? (->/c (? real? r))) (if (<  r 1) '✓ '?)]
    [('exact-positive-integer? (-≥/c (? real? r))) (if (<= r 1) '✓ '?)]
    [((-</c (? real? r)) 'exact-positive-integer?) (if (<= r 1) '✗ '?)]
    [((-≤/c (? real? r)) 'exact-positive-integer?) (if (<  r 1) '✗ '?)]
    
    ; equal?
    [((-≡/c (-b b₁)) (-≡/c (-b b₂))) (boolean->R (equal? b₁ b₂))]

    ;; default
    [(_ _)
     (cond [(equal? p q) '✓]
           [(or (and (symbol? p) (-st-p? q))
                (and (symbol? q) (-st-p? p)))
            '✗]
           [else '?])]))

(: sat-one-of : -V (Listof Base) → -R)
(define (sat-one-of V bs)
  (match V
    [(-b b) (if (member b bs) '✓ '✗)]
    [(? -●?) '?]
    [_ '✗]))

(module+ test
  (require typed/rackunit
           "../ast/definition.rkt"
           "../runtime/main.rkt"
           "for-test.rkt")
  
  ;; V ∈ p
  #|(check-✓ (p∋Vs 'not (-b #f)))
  (check-✓ (p∋Vs 'boolean? (-b #f)))
  (check-✓ (p∋Vs 'integer? (-b 1)))
  (check-✓ (p∋Vs 'real? (-b 1)))
  (check-✓ (p∋Vs 'number? (-b 1)))
  (check-✓ (p∋Vs 'procedure? (-Clo '(x) (λ _ (⊥ans)) ⊥ρ ⊤Γ)))
  (check-✓ (p∋Vs 'procedure? 'procedure?))
  (check-✓ (p∋Vs -cons? (-St -𝒾-cons (list (-α.fld -𝒾-cons 0 0 0) (-α.fld -𝒾-cons 0 0 1)))))
  (check-✗ (p∋Vs 'number? (-St -𝒾-cons (list (-α.fld -𝒾-cons 0 0 0) (-α.fld -𝒾-cons 0 0 1)))))
  (check-✗ (p∋Vs 'integer? (-b 1.5)))
  (check-✗ (p∋Vs 'real? (-b 1+1i)))
  (check-? (p∋Vs 'integer? -●/V))|#

  ;; ⊢ e
  #|(check-✓ (φs⊢e ∅ 'not))
  (check-✓ (φs⊢e ∅ (-b 0)))
  (check-✗ (φs⊢e ∅ (-b #f)))
  (check-? (φs⊢e ∅ (-x 'x)))
  (check-✗ (φs⊢e ∅ (-?@ 'not (-b 0))))
  (check-✓ (φs⊢e ∅ (-?@ 'equal? (-x 'x) (-x 'x))))
  (check-✓ (φs⊢e ∅ (-?@ '+ (-x 'x) (-x 'y))))
  (check-✗ (φs⊢e ∅ (-?@ -cons? -null)))
  (check-✗ (φs⊢e ∅ (-?@ 'null? (-?@ -cons (-b 0) (-b 1)))))|#
  
  ;; Γ ⊢ e
  (check-✓ (φs⊢e {set (assert (-?@ -cons? (-x 'x)))} (-x 'x)))
  (check-✓ (φs⊢e {set (assert (-?@ 'integer? (-x 'x)))} (-?@ 'real? (-x 'x))))
  (check-✓ (φs⊢e {set (assert (-?@ 'not (-?@ 'number? (-x 'x))))} (-?@ 'not (-?@ 'integer? (-x 'x)))))
  (check-✗ (φs⊢e {set (assert (-?@ 'not (-x 'x)))} (-x 'x)))
  (check-? (φs⊢e {set (assert (-?@ 'number? (-x 'x)))} (-?@ 'integer? (-x 'x))))

  ;; plausibility
  (check-false (plausible-W? ∅ (list (-b 1)) (-b 2)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (-b 3)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (-?@ 'values (-b 1) (-b 3))))
  (check-false (plausible-W? ∅ (list -tt) -ff))
  (check-true  (plausible-W? ∅ (list -tt) -tt))
  (check-false (plausible-W? {set (assert (-not (-x 'x)))} (list (-b 0)) (-x 'x)))
  )
