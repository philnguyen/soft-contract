#lang typed/racket/base

(provide Γ⊢t φs⊢t ⊢V p∋Vs p⇒p ps⇒p
         plausible-φs-t? plausible-W? plausible-V-t?
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

(: ⊢t : -t → -R)
;; Check if expression returns truth
(define (⊢t t)
  (match t
    [(-b b) (if b '✓ '✗)]
    [(? -•?) '?]
    [(? -v?) '✓]
    [(-t.@ f xs) (⊢@ f xs)]
    [_ '?]))

(: ⊢@ : -h (Listof -t) → -R)
  ;; Check if application returns truth
(define (⊢@ p xs)

  (match p
    [(? -st-mk?) '✓]
    [(or 'equal? 'eq? '=)
     (match xs
       [(list t₁ t₂)
        (match* (t₁ t₂)
          [((? -λ? v₁) (? -λ? v₂)) ; can't compare higher-order literals
           (if (equal? v₁ v₂) '? '✗)]
          [((? -•?) _) '?]
          [(_ (? -•?)) '?]
          [((? -v? v₁) (? -v? v₂)) (boolean->R (equal? v₁ v₂))]
          [((-x x) (-x y))
           (if (equal? x y) '✓ '?)]
          [(_ _) '?])]
       [_ #|TODO|# '?])]
    [_ '?]))

(: Γ⊢t : -Γ -?t → -R)
(define (Γ⊢t Γ t) (φs⊢t (-Γ-facts Γ) t))

(: φs⊢t : (℘ -t) -?t → -R)
(define (φs⊢t φs t)

  (when (∋ φs -ff)
    ;; Rule `{… #f …} ⊢ e : ✓` is not always desirable, because
    ;; sometimes we want `{… #f …} ⊢ (¬ e) : ✓`, which means `{… #f …} ⊢ e : ✗`
    ;; This is a problem with precision rather than soundness, but I want
    ;; (obviously) inconsistent path-conditions to not exist in the first place.
    (error 'φs⊢t "Attempt to prove/refute with inconsistent path-condition"))

  (: t⊢t : -t -t → -R)
  ;; Check if `t₂` returns truth when `t₁` does
  (define (t⊢t t₁ t₂)
    (with-debugging/off
      ((ans)
       ;; (⊢t t₂) is not redundant, because this may be just a sub-exp of the original goal
       (case (⊢t t₁)
         [(✗) '✓]
         [else
          (match (⊢t t₂)
            ['?
             (match* (t₁ t₂)
               ; t ⇒ t
               [(t t) '✓]
               ; NOTE: Don't abuse "contrapositive"
               ; (¬t₁ ⊢ ¬t₂ : ✗) does not follow from (t₂ ⊢ t₁ : ✗)
               [((-t.not t₁*) (-t.not t₂*))
                (case (t⊢t t₂* t₁*)
                  [(✓)   '✓]
                  [(✗ ?) '?])]
               [(t₁ (-t.not t₂*))
                (not-R (t⊢t t₁ t₂*))]
               [((-t.@ (? -h? p) (list t)) (-t.@ (? -h? q) (list t)))
                (p⇒p p q)] ; FIXME
               [((-t.@ (? -o? p) (list t)) t)
                (cond
                  [(eq? 'not p) '✗]
                  [(and (symbol? p) (boolean-excludes? p)) '✓]
                  [(-st-p? p) '✓]
                  [else '?])]
               [((-t.@ (? op-≡?) (list t₁ t₂)) (-t.@ (? -o? p) (list t₁)))
                (⊢@ p (list t₂))]
               [((-t.@ (? op-≡?) (list t₁ t₂)) (-t.@ (? -o? p) (list t₂)))
                (⊢@ p (list t₁))]
               [((-t.@ (? op-≡?) (list t (-b b₁)))
                 (-t.@ (? op-≡?) (list t (-b b₂))))
                (boolean->R (equal? b₁ b₂))]
               [((-t.@ (? op-≡?) (list (-b b₁) t))
                 (-t.@ (? op-≡?) (list (-b b₂) t)))
                (boolean->R (equal? b₁ b₂))]
               ;; Ariths
               [((or (-t.@ (? op-≡?) (list t (-b b₁)))
                     (-t.@ (? op-≡?) (list (-b b₁) t)))
                 (-t.@ (? -special-bin-o? o) (list t (-b b₂))))
                (p⇒p (-≡/c b₁) ((bin-o->h o) b₂))]
               [((or (-t.@ (? op-≡?) (list t (-b b₁)))
                     (-t.@ (? op-≡?) (list (-b b₁) t)))
                 (-t.@ (? -special-bin-o? o) (list (-b b₂) t)))
                (p⇒p (-≡/c b₁) ((bin-o->h (flip-bin-o o)) b₂))]
               [(_ _) '?])]
            [R R])]))
      (printf "~a ⊢ ~a : ~a~n" (show-t t₁) (show-t t₂) ans)))

  (with-debugging/off
    ((ans)
     (cond
       [t
        (first-R
         (⊢t t)
         (match t
           [_ #:when (∋ φs         t ) '✓]
           [_ #:when (∋ φs (-t.not t)) '✗]
           [(-t.not t*) #:when (∋ φs t*) '✗]
           [else '?])
         (for*/fold ([R : -R '?])
                    ([φ (in-set φs)] #:when (eq? '? R))
           (t⊢t φ t))
         '?)]
       [else '?]))
    (printf "~a ⊢ ~a : ~a~n" (set-map φs show-t) (show-t t) ans)))

(: p⇒p : -h -h → -R)
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
    [((-not/c (? -h? p)) (-not/c (? -h? q)))
     (case (p⇒p q p)
       [(✓) '✓]
       [else '?])]
    [(p (-not/c (? -h? q)))
     (not-R (p⇒p p q))]
    [((-not/c (? -h? p)) q)
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
    [((-≡/c b₁) (-≡/c b₂)) (boolean->R (equal? b₁ b₂))]
    [((-≡/c b₁) (-≢/c b₂)) (boolean->R (not (equal? b₁ b₂)))]
    [((-≡/c (? real? b₁)) (-</c (? real? b₂))) (boolean->R (<  b₁ b₂))]
    [((-≡/c (? real? b₁)) (-≤/c (? real? b₂))) (boolean->R (<= b₁ b₂))]
    [((-≡/c (? real? b₁)) (->/c (? real? b₂))) (boolean->R (>  b₁ b₂))]
    [((-≡/c (? real? b₁)) (-≥/c (? real? b₂))) (boolean->R (>= b₁ b₂))]

    ;; default
    [(_ _)
     (cond [(equal? p q) '✓]
           [(or (and (symbol? p) (-st-p? q))
                (and (symbol? q) (-st-p? p)))
            '✗]
           [else '?])]))

(define (plausible-φs-t? [φs : (℘ -t)] [t : -?t]) : Boolean
  (with-debugging/off
    ((a) (not (eq? '✗ (φs⊢t φs t))))
    (printf "plausible-φs-s: ~a ⊢ ~a : ~a~n"
            (set-map φs show-e)
            (show-s s)
            a)))

(: plausible-W? : (℘ -t) (Listof -V) -?t → Boolean)
;; Check if value(s) `Vs` can instantiate symbol `s` given path condition `φs`
;; - #f indicates a definitely bogus case
;; - #t indicates (conservative) plausibility
(define (plausible-W? φs Vs t)
  (match* (Vs t)
    [(_ (-t.@ 'values ts))
     (and (= (length Vs) (length ts))
          (for/and : Boolean ([V Vs] [t ts])
            (plausible-V-t? φs V t)))]
    [((list V) _) #:when t
     (plausible-V-t? φs V t)]
    ; length(Vs) ≠ 1, length(s) = 1
    ; TODO: below doesn't seem true anymore. Check
    [(_ (or (? -v?) (-t.@ (? -prim?) _))) #f]
    [(_ _) #t]))

(: plausible-V-t? : (℘ -t) -V -?t → Boolean)
(define (plausible-V-t? φs V t)
  (define-syntax-rule (with-prim-checks p? ...)
    (cond
      [t
       (match V
         [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _)) #:when 𝒾
          (plausible-φs-t? φs (?t@ (-st-p 𝒾) t))]
         [(or (? -Vector?) (? -Vector^?) (? -Vector/guard?))
          (plausible-φs-t? φs (?t@ 'vector? t))]
         [(or (? -Clo?) (? -Case-Clo?) (? -Ar?) (? -o?))
          (plausible-φs-t? φs (?t@ 'procedure? t))]
         [(-b (? p?))
          (and (plausible-φs-t? φs (?t@ 'p? t))
               (plausible-φs-t? φs (?t@ 'equal? t V))
               (implies (-b? t) (equal? V t)))] ...
         #|;; FIXME tmp. hack
         [(-b (and (? number?) (? exact?)))
          (and (plausible-φs-t? φs (?t@ 'exact? s))
               (plausible-φs-t? φs (?t@ 'equal? s V))
               (implies (-b? s) (equal? V s)))]
         [(-b (and (? number?) (? inexact?)))
          (and (plausible-φs-t? φs (?t@ 'inexact? s))
               (plausible-φs-t? φs (?t@ 'equal? s V))
               (implies (-b? s) (equal? V s)))]
         |#
         ;; end tmp. hack
         [(or (? -=>_?) (? -St/C?) (? -x/C?))
          (for/and : Boolean ([p : -o '(procedure? p? ...)])
            (case (φs⊢t φs (?t@ p t))
              [(✓)   #f]
              [(✗ ?) #t]))]
         [(-b (list))
          (plausible-φs-t? φs (?t@ 'null? t))]
         [(? -v? v)
          (plausible-φs-t? φs (?t@ 'equal? t v))]
         [(-● ps)
          (not (for/or : Boolean ([p ps])
                 (match p
                   [(? -o? o) (equal? '✗ (φs⊢t φs (-t.@ o (list t))))]
                   [_ #f])))]
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
     (or (for/or : (U #f '✓ '✗) ([p ps])
           (case (p⇒p p 'not)
             [(✓) '✗]
             [(✗) '✓]
             [(?) #f]))
         '?)]
    [_ '✓]))

(: p∋Vs : -σ (U -h -v -V) -V * → -R)
;; Check if value satisfies predicate
(define (p∋Vs σ p . Vs)
  
  (define (check-proc-arity-1 [V : -V]) : -R
    (match (p∋Vs σ 'procedure? V)
      ['✓ (boolean->R (arity-includes? (assert (V-arity V)) 1))]
      [ans ans]))

  (with-debugging/off
    ((R) (ann (match Vs
    [(list (-● ps)) #:when (-h? p)
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
        
        (with-base-predicates (not
                               exact-positive-integer?
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
                [(list _ ... (-≡/c (? real? a)) _ ...) #:when a (if (<  a b) '✓ '✗)]
                [_ '?])]
             [(list (-b (? real? b)) (-● ps))
              #:when (and (<= b 0)
                          (∋ ps 'exact-positive-integer?))
              '✓]
             [_ '?])]
          [(<=)
           (match Vs
             [(list (-● ps) (-b (? real? b)))
              (match (set->list ps)
                [(list _ ... (-</c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                [(list _ ... (-≤/c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                [(list _ ... (->/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                [(list _ ... (-≥/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                [(list _ ... (-≡/c (? real? a)) _ ...) #:when a (if (<= a b) '✓ '✗)]
                [_ '?])]
             [(list (-b (? real? b)) (-● ps))
              #:when (and (<= b 0)
                          (∋ ps 'exact-nonnegative-integer?))
              '✓]
             [_ '?])]
          [(>) (p∋Vs σ '< (second Vs) (first Vs))]
          [(>=) (p∋Vs σ '<= (second Vs) (first Vs))]
          [(= equal? eq? char=? string=?)
           (match Vs
             [(list (-b b₁) (-b b₂))   (boolean->R (equal? b₁ b₂))]
             [(list (-● ps) (-b b)) (ps⇒p ps (-≡/c b))]
             [(list (-b b) (-● ps)) (ps⇒p ps (-≡/c b))]
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
          [else '?])]
       [(-not/c (? -h? p))
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
       [(-≡/c b₁)
        (match-define (list V) Vs)
        (p∋Vs σ 'equal? (-b b₁) V)]
       [_ '?])]) -R))
    (when (equal? p 'equal?)
      (printf "~a ∋ ~a ? : ~a~n" p (map show-V-or-v Vs) R))))

(: ps⇒p : (℘ -h) -h → -R)
(define (ps⇒p ps p)
  (or (for/or : (U #f '✓ '✗) ([q ps] #:when (-h? q))
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
                    (-≡/c (? (>=/c 0))))))
            '✓]
           [(and (∋ ps 'integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (-</c (? (<=/c 0)))
                    (-≤/c (? (</c  0)))
                    (-≡/c (? (</c  0))))))
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
                    (-≡/c (? (>/c 0)))
                    (-≢/c 0))))
            '✓]
           [(and (∋ ps 'integer?)
                 (for/or : Boolean ([p ps])
                   (match?
                    p
                    (->/c (? (>=/c 0)))
                    (-≥/c (? (>/c 0)))
                    (-≡/c (? (>/c 0))))))
            '✓]
           [else '?])]
        [else '?])))

(: sat-one-of : -V (Listof Base) → -R)
(define (sat-one-of V bs)
  (match V
    [(-b b) (if (member b bs) '✓ '✗)]
    [(? -●?) '?]
    [_ '✗]))

(: V≡ : -V -V → -R)
;; Check if 2 values are `equal?`
(define V≡
  (match-lambda**
   [((-b x₁) (-b x₂)) (boolean->R (equal? x₁ x₂))]
   [(_ _) '?]))

(module+ test
  (require typed/rackunit
           "../ast/definition.rkt"
           "../runtime/main.rkt"
           "for-test.rkt")
  
  ;; V ∈ p
  (check-✓ (p∋Vs ⊥σ 'not (-b #f)))
  (check-✓ (p∋Vs ⊥σ 'boolean? (-b #f)))
  (check-✓ (p∋Vs ⊥σ 'integer? (-b 1)))
  (check-✓ (p∋Vs ⊥σ 'real? (-b 1)))
  (check-✓ (p∋Vs ⊥σ 'number? (-b 1)))
  (check-✓ (p∋Vs ⊥σ 'procedure? (-Clo '(x) (λ _ (error "who cares")) ⊥ρ ⊤Γ)))
  (check-✓ (p∋Vs ⊥σ 'procedure? 'procedure?))
  (check-✓ (p∋Vs ⊥σ -cons? (-St -𝒾-cons (list ⟪α⟫ₕᵥ ⟪α⟫ₕᵥ))))
  (check-✗ (p∋Vs ⊥σ -cons? -null))
  (check-✗ (p∋Vs ⊥σ 'number? (-St -𝒾-cons (list ⟪α⟫ₕᵥ ⟪α⟫ₕᵥ))))
  (check-✗ (p∋Vs ⊥σ 'integer? (-b 1.5)))
  (check-✗ (p∋Vs ⊥σ 'real? (-b 1+1i)))
  (check-? (p∋Vs ⊥σ 'integer? -●.V))

  ;; ⊢ e
  (check-✓ (φs⊢t ∅ 'not))
  (check-✓ (φs⊢t ∅ (-b 0)))
  (check-✗ (φs⊢t ∅ (-b #f)))
  (check-? (φs⊢t ∅ (-x 'x)))
  (check-✗ (φs⊢t ∅ (?t@ 'not (-b 0))))
  (check-✓ (φs⊢t ∅ (?t@ 'equal? (-x 'x) (-x 'x))))
  ;; no longer need for aggressive simplification at symbol level
  (check-✓ (φs⊢t ∅ (?t@ '+ (-x 'x) (-x 'y))))
  (check-✗ (φs⊢t ∅ (?t@ -cons? -null)))
  (check-✗ (φs⊢t ∅ (?t@ 'null? (?t@ -cons (-b 0) (-b 1)))))
  
  ;; Γ ⊢ e
  (check-✓ (φs⊢t {set (assert (?t@ -cons? (-x 'x)))} (-x 'x)))
  ;; Next two won't work now due to base assumptions not loaded at this stage
  (check-✓ (φs⊢t {set (assert (?t@ 'integer? (-x 'x)))} (?t@ 'real? (-x 'x))))
  (check-✓ (φs⊢t {set (assert (?t@ 'not (?t@ 'number? (-x 'x))))} (?t@ 'not (?t@ 'integer? (-x 'x)))))
  (check-✗ (φs⊢t {set (assert (?t@ 'not (-x 'x)))} (-x 'x)))
  (check-? (φs⊢t {set (assert (?t@ 'number? (-x 'x)))} (?t@ 'integer? (-x 'x))))

  ;; plausibility
  (check-false (plausible-W? ∅ (list (-b 1)) (-b 2)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (-b 3)))
  (check-false (plausible-W? ∅ (list (-b 1) (-b 2)) (?t@ 'values (-b 1) (-b 3))))
  (check-false (plausible-W? ∅ (list -tt) -ff))
  (check-true  (plausible-W? ∅ (list -tt) -tt))
  ;; Next line doens't work because (number? ⇒ (not/c not)) not loaded at this stage
  (check-false (plausible-W? {set (assert (-t.not (-x 'x)))} (list (-b 0)) (-x 'x)))
  )
