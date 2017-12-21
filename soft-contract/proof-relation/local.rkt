#lang typed/racket/base

(provide local-prover@)

(require (for-syntax racket/base
                     racket/contract
                     "../utils/pretty.rkt")
         typed/racket/unit
         racket/match
         racket/set
         racket/string
         racket/bool
         racket/list
         syntax/parse/define
         (only-in racket/list first second)
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit local-prover@
  (import static-info^ prims^ path^ sto^ val^ pretty-print^ sat-result^)
  (export local-prover^)
  (init-depend prims^)

  ;; Check whether predicate excludes boolean
  (define boolean-excludes? (set->predicate (get-exclusions 'boolean?)))

  (: p⇒p : -h -h → -R)
  ;; Return whether predicate `p` definitely implies or excludes `q`.
  (define (p⇒p p q)

    ;; Whether predicate only covers base types
    (define (base-only? [p : -h]) : Boolean
      (and (symbol? p) (not (memq p '(list? struct?)))))
    
    (match* (p q)
      [(_ 'any/c) '✓]
      [('none/c _) '✓]
      [(_ 'none/c) '✗]
      [('any/c _) '?]
      [((? symbol? p) (? symbol? q)) (o⇒o p q)]
      [(p 'values) (if (eq? p 'not) '✗ '✓)]
      [((-st-p 𝒾₁) (-st-p 𝒾₂)) (boolean->R (𝒾₁ . substruct? . 𝒾₂))]

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
      [(_ 'zero?) (p⇒p p (-≡/c (-b 0)))]
      [('zero? _) (p⇒p (-≡/c (-b 0)) q)]
      ; < and <
      [((-</c (? real? a)) (-</c (? real? b))) (if (<= a b) '✓ '?)]
      [((-≤/c (? real? a)) (-≤/c (? real? b))) (if (<= a b) '✓ '?)]
      [((-</c (? real? a)) (-≤/c (? real? b))) (if (<= a b) '✓ '?)]
      [((-≤/c (? real? a)) (-</c (? real? b))) (if (<  a b) '✓ '?)]
      ; > and >
      [((->/c (? real? a)) (->/c (? real? b))) (if (>= a b) '✓ '?)]
      [((-≥/c (? real? a)) (-≥/c (? real? b))) (if (>= a b) '✓ '?)]
      [((->/c (? real? a)) (-≥/c (? real? b))) (if (>= a b) '✓ '?)]
      [((-≥/c (? real? a)) (->/c (? real? b))) (if (>  a b) '✓ '?)]
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
      ; _ -> real?
      [((or (? -</c?) (? ->/c?) (? -≤/c?) (? -≥/c?)) (or 'real? 'number?)) '✓]
      [((-≡/c t) o) (p∋V ⊥σ φ₀ o t)]
      
      ; equal?
      [((-≡/c b₁) (-≡/c b₂)) (boolean->R (equal? b₁ b₂))]
      [((-</c (? real? b₁)) (-≡/c (-b (? real? b₂)))) #:when (<= b₁ b₂) '✗]
      [((-≤/c (? real? b₁)) (-≡/c (-b (? real? b₂)))) #:when (<  b₁ b₂) '✗]
      [((->/c (? real? b₁)) (-≡/c (-b (? real? b₂)))) #:when (>= b₁ b₂) '✗]
      [((-≥/c (? real? b₁)) (-≡/c (-b (? real? b₂)))) #:when (>  b₁ b₂) '✗]
      ; 
      [((-≡/c (-b (? real? b₁))) (-</c (? real? b₂))) (boolean->R (<  b₁ b₂))]
      [((-≡/c (-b (? real? b₁))) (-≤/c (? real? b₂))) (boolean->R (<= b₁ b₂))]
      [((-≡/c (-b (? real? b₁))) (->/c (? real? b₂))) (boolean->R (>  b₁ b₂))]
      [((-≡/c (-b (? real? b₁))) (-≥/c (? real? b₂))) (boolean->R (>= b₁ b₂))]

      ;; default
      [(p p) '✓]
      [((? base-only?) (? -st-p?)) '✗]
      [((? -st-p?) (? base-only?)) '✗]
      [(_ _) '?]))

  ;; Check if value represents truth
  (define ⊢U : (-U → -R)
    (match-lambda
      [(-b #f) '✗]
      [(-● ps) (not-R (ps⇒p ps 'not))]
      [_ '✓]))

  (: lift-p∋V : (-σ -φ -h -V * → -R) → -σ -φ -h -V^ * → -R)
  (define ((lift-p∋V p∋V₁) σ φ p . V^s)
    (let go ([V^s : (Listof -V^) V^s] [Vs-rev : (Listof -V) '()])
      (match V^s
        ['() (apply p∋V₁ σ φ p (reverse Vs-rev))]
        [(cons V^₁ V^s*)
         ((inst R⊔* -V) (λ (V) (go V^s* (cons V Vs-rev))) V^₁)]))) 

  (: p∋V : -σ -φ -h -V * → -R)
  (define (p∋V σ φ p . Vs)

    (define (check-proc-arity-1 [V : -V])
      (case (p∋V σ φ 'procedure? V)
        [(✓) (arity-includes? (assert (V-arity V)) 1)]
        [else #f]))

    (match Vs
      [(list (-t.@ o xs)) #:when (equal? p 'values) (apply p∋V σ φ o xs)]
      [(list (-t.@ o xs)) #:when (equal? p 'not) (not-R (apply p∋V σ φ o xs))]
      [(or (list (? -t? t) (-b (? boolean? b)))
           (list (-b (? boolean? b)) (? -t? t)))
       #:when (and (equal? p 'equal?) t)
       (case (p∋V σ φ 'boolean? t)
         [(✓) (p∋V σ φ (if b 'values 'not) t)]
         [(✗) '✗]
         [(?) '?])]
      [(list (? -t? t) (? -t? t))
       #:when (equal? p 'equal?)
       '✓]
      
      [(list (-● ps)) (ps⇒p ps p)]
      [(and (list (-t.@ k _))
            (app (match-lambda [(list (-t.@ k _)) (p∋k p k)])
                 (and R (or '✓ '✗))))
       R]
      [(list t t) #:when (equal? p '=) '✓]
      [Vs
       #:when (and (andmap -t? Vs) (not (andmap -b? Vs)))
       (case p
         [(list?) (check-proper-list σ φ (car Vs))] ; `list?` is the only deep predicate
         [else
          (define-values (h t)
            (match* (p Vs)
              [('>  (list t₁ t₂)) (if (-b? t₁) (values (-</c t₁) t₂) (values (->/c t₂) t₁))]
              [('>= (list t₁ t₂)) (if (-b? t₁) (values (-≤/c t₁) t₂) (values (-≥/c t₂) t₁))]
              [('<  (list t₁ t₂)) (if (-b? t₁) (values (->/c t₁) t₂) (values (-</c t₂) t₁))]
              [('<= (list t₁ t₂)) (if (-b? t₁) (values (-≥/c t₁) t₂) (values (-≤/c t₂) t₁))]
              [((or '= 'equal? 'eq? 'eqv? 'string=? 'char=?) (list t₁ t₂)) 
               (if (-b? t₁) (values (-≡/c t₁) t₂) (values (-≡/c t₂) t₁))]
              [('arity-includes? (list t (-b (? Arity? a)))) (values (-arity-includes/c a) t)]
              [(p (list t)) (values p t)]
              [(_ _) (error 'p∋V^ "missing conversion for ~a ~a" (show-h p) (map show-t Vs))]))
          (ps⇒p (hash-ref (-φ-condition φ) t mk-∅) h)])]
      [_
       (match p
         [(? -st-mk?) '✓]
         [(? -st-mut?) '✓]
         [(? -st-ac?) '✓]
         [(-st-p 𝒾)
          (match Vs
            [(list (or (-St 𝒾* _) (-St* (-St/C _ 𝒾* _) _ _)))
             (boolean->R (𝒾* . substruct? . 𝒾))]
            [_ '✗])]
         [(-One-Of/C bs) (sat-one-of (car Vs) bs)]
         [(? symbol?)
          (define-simple-macro (with-base-predicates ([guard:id ... o?:id] ...) clauses ...)
            (case p
              [(o?)
               (match Vs
                 [(list (-b (and b (? guard) ...))) (boolean->R (o? b))]
                 [_ '✗])] ...
              clauses ...))

          (: check-one-of : (-V → Boolean) * → -R)
          (define (check-one-of . ps)
            (match Vs
              [(list V)
               (or (for/or : (Option '✓) ([p (in-list ps)])
                     (and (p V) '✓))
                   '✗)]
              [_ '✗]))

          (with-base-predicates ([not]
                                 [exact-positive-integer?]
                                 [exact-nonnegative-integer?]
                                 [exact-integer?]
                                 [number? zero?]
                                 [exact-integer? even?]
                                 [exact-integer? odd?]
                                 [number? exact?]
                                 [number? inexact?]
                                 [integer?]
                                 [inexact-real?]
                                 [real?]
                                 [number?]
                                 [null?]
                                 [boolean?]
                                 [non-empty-string?]
                                 [path-string?]
                                 [string?]
                                 [char?]
                                 [symbol?]
                                 [void?]
                                 [eof-object?]
                                 [regexp?]
                                 [pregexp?]
                                 [byte-regexp?]
                                 [byte-pregexp?])
            ;; Insert manual rules here
            [(values)
             (match Vs
               [(list (-b b)) (if b '✓ '✗)]
               [_ '✓])]
            [(procedure?) (check-one-of -o? -Fn? -Ar? -Not/C? -One-Of/C?
                                        (λ (V) (match? V (-And/C #t _ _) (-Or/C #t _ _) (-St/C #t _ _))))]
            [(vector?) (check-one-of -Vector? -Vector^? -Vector/guard?)]
            [(hash?) (check-one-of -Hash^? -Hash/guard?)]
            [(set? generic-set?) (check-one-of -Set^? -Set/guard?)]
            [(contract?) (check-one-of -=>_? -And/C? -Or/C? -Not/C? -Not/C?
                                       -Vectorof? -Vector/C? -St/C? -x/C? -Hash/C? -Set/C?
                                       -∀/C? -Seal/C? -b?
                                       check-proc-arity-1)]
            [(flat-contract?) (check-one-of -b? check-proc-arity-1)]
            [(any/c)
             (match Vs
               [(list (? -Sealed?)) '?] ; pretend we don't know `any/c` is the only top type
               [_ '✓])]
            [(none/c) '✗]
            [(arity-includes?)
             (match Vs
               [(list (-b (? Arity? a)) (-b (? Arity? b)))
                (boolean->R (arity-includes? a b))]
               [_ '?])]
            [(immutable?)
             (define (check-all-immutable [α : ⟪α⟫])
               ((inst R⊔* -V) (λ (V) (p∋V σ φ 'immutable? V)) (σ@ σ (-φ-cache φ) α)))
             
             (match Vs
               [(list (-b b)) (boolean->R (immutable? b))]
               [(list (-Hash^ _ _ im?)) (boolean->R im?)]
               [(list (-Hash/guard _ α _)) (check-all-immutable α)]
               [(list (-Set^ _ im?)) (boolean->R im?)]
               [(list (-Set/guard _ α _)) (check-all-immutable α)]
               ;; vectors always false for now because no support for immutable vectors
               [(list (or (? -Vector?) (? -Vector^?) (? -Vector/guard?))) '✗]
               [_ '?])]
            [(<)
             (ann (match Vs
               [(list (-b (? real? b₁)) (-b (? real? b₂)))
                (boolean->R (< b₁ b₂))]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (-≥/c (? real? b₂)) _ ...))))
                #:when (< b₁ b₂)
                '✓]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (->/c (? real? b₂)) _ ...))))
                #:when (<= b₁ b₂)
                '✓]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (or (-≤/c (? real? b₂))
                                                         (-</c (? real? b₂))) _ ...))))
                #:when (and b₂ (<= b₁ b₂))
                '✗]
               [(list (-● ps) (-b (? real? b)))
                (match (set->list ps)
                  [(list _ ... (-</c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                  [(list _ ... (-≤/c (? real? a)) _ ...) (if (<  a b) '✓ '?)]
                  [(list _ ... (->/c (? real? a)) _ ...) (if (>= a b) '✗ '?)]
                  [(list _ ... (-≥/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                  [(list _ ... (-b   (? real? a)) _ ...) #:when a (if (<  a b) '✓ '✗)]
                  [_ '?])]
               [(list (-b (? real? b)) (-● ps))
                #:when (and (< b 0)
                            (∋ ps 'exact-nonnegative-integer?))
                '✓]
               [(list (-b (? real? b)) (-● ps))
                #:when (and (<= b 0)
                            (∋ ps 'exact-positive-integer?))
                '✓]
               [_ '?]) -R)]
            [(<=)
             (ann (match Vs
               [(list (-b (? real? b₁)) (-b (? real? b₂)))
                (boolean->R (<= b₁ b₂))]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (or (-≥/c (? real? b₂))
                                                         (->/c (? real? b₂))) _ ...))))
                #:when (and b₂ (>= b₂ b₁))
                '✓]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (-</c (? real? b₂)) _ ...))))
                #:when (and b₂ (<= b₂ b₁))
                '✗]
               [(list (-● ps) (-b (? real? b)))
                (match (set->list ps)
                  [(list _ ... (-</c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                  [(list _ ... (-≤/c (? real? a)) _ ...) (if (<= a b) '✓ '?)]
                  [(list _ ... (->/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                  [(list _ ... (-≥/c (? real? a)) _ ...) (if (>  a b) '✗ '?)]
                  [(list _ ... (-b   (? real? a)) _ ...) #:when a (if (<= a b) '✓ '✗)]
                  [_ '?])]
               [(list (-b (? real? b)) (-● ps))
                #:when (and (<= b 0) (∋ ps 'exact-nonnegative-integer?))
                '✓]
               [(list (-b (? real? b)) (-● ps))
                #:when (and (<= b 1) (∋ ps 'exact-positive-integer?))
                '✓]
               [_ '?]) -R)]
            [(>) (p∋V σ φ '< (second Vs) (first Vs))]
            [(>=) (p∋V σ φ '<= (second Vs) (first Vs))]
            [(= equal? eq? char=? string=?)
             (match Vs
               [(list (-b b₁) (-b b₂)) (boolean->R (equal? b₁ b₂))]
               [(list (-● ps) (? -b? b)) (ps⇒p ps (-≡/c b))]
               [(list (? -b? b) (-● ps)) (ps⇒p ps (-≡/c b))]
               [(list (? -o? o₁) (? -o? o₂)) (boolean->R (equal? o₁ o₂))] 
               [_ '?])]
            [(list?) (check-proper-list σ φ (car Vs))]
            [(port? input-port? output-port?) '✗]
            [else (if (boolean-excludes? (get-conservative-range p)) '✓ '?)])]
         [(-not/c (? -h? p)) (not-R (apply p∋V σ φ p Vs))]
         [(-≥/c b) (p∋V σ φ '>= (car Vs) b)]
         [(->/c b) (p∋V σ φ '> (car Vs) b)]
         [(-</c b) (p∋V σ φ '< (car Vs) b)]
         [(-≤/c b) (p∋V σ φ '<= (car Vs) b)]
         [(-≡/c b) (p∋V σ φ 'equal? b (car Vs))]
         [_ '?])]))

  (: p∋k : -h -h → -R)
  (define (p∋k p k)
    (match k
      [(? symbol? o) (p⇒p (get-conservative-range k) p)]
      [(-st-mk 𝒾) (p⇒p (-st-p 𝒾) p)]
      [(? -st-ac?) '?]
      [(? -st-mut?) (p⇒p 'void? p)]
      [_ (p⇒p 'boolean? p)]))

  (define p∋V^ (lift-p∋V p∋V))

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
                      (-b   (? (>=/c 0))))))
              '✓]
             [(and (∋ ps 'integer?)
                   (for/or : Boolean ([p ps])
                     (match?
                      p
                      (-</c (? (<=/c 0)))
                      (-≤/c (? (</c  0)))
                      (-b   (? (</c  0))))))
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
                      (-b   (? (>/c 0)))
                      (-not/c (-b 0)))))
              '✓]
             [(and (∋ ps 'integer?)
                   (for/or : Boolean ([p ps])
                     (match?
                      p
                      (->/c (? (>=/c 0)))
                      (-≥/c (? (>/c 0)))
                      (-b   (? (>/c 0))))))
              '✓]
             [else '?])]
          [(any/c) '✓]
          [(none/c) '✗]
          [else '?])))

  (: check-proper-list : -σ -φ -V → -R)
  (define (check-proper-list σ φ V)
    (match-define (-φ Γ δσ) φ)
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
              (for/seteq: : (℘ -R) ([Vᵣ (σ@ σ δσ ⟪α⟫)])
                (check Vᵣ)))]))

    (define (check [V : -V]) : -R
      (match V
        [(-Cons _ α) (check-⟪α⟫ α)]
        [(-Cons* α) (check-⟪α⟫ α)]
        [(-b b) (boolean->R (null? b))]
        [(-● ps)
         (cond
           [(∋ ps 'list?) '✓]
           [(set-empty?
             (∩ ps {set 'number? 'integer? 'real? 'exact-nonnegative-integer?
                        'string? 'symbol?}))
            '?]
           [else '✗])]
        [(? -t? t)
         (case (ps⇒p (hash-ref Γ t mk-∅) 'list?)
           [(✓) '✓]
           [(✗) '✗]
           [(?) (case (ps⇒p (hash-ref Γ t mk-∅) -cons?)
                  [(✓) (define t.cdr (-t.@ -cdr (list t)))
                       (if (hash-has-key? Γ t.cdr) (check t.cdr) '?)]
                  [(✗) '✗]
                  [(?) '?])])]
        [_ '✗]))
    (check V))

  (: sat-one-of : -V^ (℘ Base) → -R)
  (define (sat-one-of V^ bs)
    ((inst R⊔* -V) (λ (V) (sat-one-of₁ V bs)) V^))

  (: sat-one-of₁ : -V (℘ Base) → -R)
  (define (sat-one-of₁ V bs)
    (match V
      [(-b b) (if (∋ bs b) '✓ '✗)]
      [(? -●?) '?]
      [_ '✗]))

  ;; Check if 2 values are `equal?`
  (define V≡ : (-V -V → -R)
    (match-lambda**
     [((-b x₁) (-b x₂)) (boolean->R (equal? x₁ x₂))]
     [(_ _) '?]))

  (define V-arity : (case->
                     [-Clo → Arity]
                     [-Case-Clo → Arity]
                     [-V → (Option Arity)])
    (match-lambda
      [(-Clo xs _ _) (shape xs)]
      [(-Case-Clo cases) (normalize-arity (map V-arity cases))]
      [(-Fn● arity _) arity]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?) (-St/C #t _ _) (? -One-Of/C?)) 1]
      [(-Ar guard _ _) (guard-arity guard)]
      [(? -st-p?) 1]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (prim-arity o)]
      [(-● _) #f]
      [(? integer?) #f]
      [V
       #:when (not (or (-Clo? V) (-Case-Clo? V))) ; to convince TR
       (log-warning "Warning: call `V-arity` on an obviously non-procedure ~a" (show-V V))
       #f])) 
  )
