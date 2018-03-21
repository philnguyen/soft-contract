#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/sequence
         racket/list
         racket/splicing
         racket/string
         syntax/parse/define
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit local-prover-core@
  (import static-info^
          sto^ evl^ val^ prims^
          sat-result^)
  (export local-prover-core^)
  (init-depend prims^)

  (: check : Σ Φ V (Listof V) → ?Dec)
  (define (check Σ Φ P₀ Vs₀)

    (: check-equal* : (Listof α) (Listof α) → ?Dec)
    (define (check-equal* αs₁ αs₂)
      (for/fold ([d : ?Dec '✓])
                ([α₁ (in-list αs₁)]
                 [α₂ (in-list αs₂)]
                 #:break (not (equal? d '✓)))
        (define Vs₁ (Σᵥ@ Σ α₁))
        (define Vs₂ (Σᵥ@ Σ α₂))
        (define ⊔* (inst ⊔*/set V))
        (⊔* (λ (V₁) (⊔* (λ (V₂) (go 'equal? (list V₁ V₂))) Vs₂)) Vs₂)))

    (: go : V (Listof V) → ?Dec)
    (define (go P Vs)
      (cond
        [(and (P? P)
              (andmap S? Vs)
              (or (Ps⊢P (Φ@ Φ Vs) P)
                  (neg (Ps⊢P (Φ@ Φ Vs) (P:¬ P)))))]
        [else
         (match* (P Vs)
           [('values (list (S:@ Q Vs*))) (go Q Vs*)]
           [('not    (list (S:@ Q Vs*))) (neg (go Q Vs*))]
           [('equal? (or (list (? S? S) (? -b? b)) (list (? -b? b) (? S? S))))
            #:when (and S b)
            (match (go 'boolean? (list S))
              [✓ (go (if b 'values 'not) (list S))]
              [d d])]
           [('equal? (list (? S? S) (? S? S))) '✓]
           [('equal? (list (St 𝒾 αs₁) (St 𝒾 αs₂))) (check-equal* αs₁ αs₂)]
           [((? P?) (list (-● Ps))) (Ps⊢P Ps P)]
           [(_ (and (list (S:@ k _)
                          (app (match-lambda
                                 [(list (S:@ k _)) (k . check-range-in . P)])
                               (and d (? values))))))
            d]
           [('= (list V V)) '✓]
           [((? P?) _)
            #:when (and (andmap S? Vs) (not (andmap -b? Vs)))
            (case P
              [(list?) (check-proper-list Σ Φ (car Vs))]
              [else
               (define-values (P* V*)
                 (match* (P Vs)
                   [('>  (list (-b (? real? r)) S)) (values (P:< r) S)]
                   [('>  (list S (-b (? real? r)))) (values (P:> r) S)]
                   [('>= (list (-b (? real? r)) S)) (values (P:≤ r) S)]
                   [('>= (list S (-b (? real? r)))) (values (P:≥ r) S)]
                   [('<  (list (-b (? real? r)) S)) (values (P:> r) S)]
                   [('<  (list S (-b (? real? r)))) (values (P:< r) S)]
                   [('<= (list (-b (? real? r)) S)) (values (P:≥ r) S)]
                   [('<= (list S (-b (? real? r)))) (values (P:≤ r) S)]
                   [((or '= 'equal? 'eq? 'eqv? 'string=? 'char=?)
                     (or (list (-b b) S) (list S (-b b))))
                    #:when (and S b)
                    (values (P:≡ b) S)]
                   [(Q (list S)) (values Q S)]
                   [(_ _) (error 'check "missing conversion for ~a ~a" P Vs)]))
               (Ps⊢P (Φ@ Φ (list V*)) P*)])]
           [((or (? -st-mk?) (? -st-mut?)) _) '✓]
           [((-st-p 𝒾) Vs)
            (match Vs
              [(list (or (St 𝒾* _) (X/G _ (St/C _ 𝒾* _) _)))
               (bool->Dec (and 𝒾* (𝒾* . substruct? . 𝒾)))]
              [_ '✗])]
           [((One-Of/C bs) _) (check-one-of (car Vs) bs)]
           [((? symbol?) _)
            (define-simple-macro (with-base-predicates ([g:id ... o?:id] ...)
                                   c ...)
              (case P
                [(o?)
                 (match Vs
                   [(list (-b (and b (? g) ...))) (bool->Dec (o? b))]
                   [_ '✗])] ...
                c ...))
            (define (proc-arity-1? [V : V])
              (and (equal? '✓ (go 'procedure? (list V)))
                   (arity-includes? (assert (V-arity V)) 1)))
            (: check-among : (V → Boolean) * → ?Dec)
            (define (check-among . ps)
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
              ;; Manual cases
              [(values)
               (match Vs
                 [(list (-b b)) (if b '✓ '✗)]
                 [_ '✗])]
              [(procedure?)
               (check-among -o? Fn? Not/C? One-Of/C?
                            (match-λ? (X/G _ (? Fn/C?) _)
                                      (And/C #t _ _)
                                      (Or/C #t _ _)
                                      (St/C #t _ _)))]
              [(vector?)
               (check-among Vect? Vect^?
                            (match-λ? (X/G _ (or (? Vect/C?) (? Vectof?)) _)))]
              [(hash?) (check-among Hash^? (match-λ? (X/G _ (? Hash/C?) _)))]
              [(set? generic-set?) (check-among Set^? (match-λ? (X/G _ (? Set/C?) _)))]
              [(contract?) (check-among Fn/C? And/C? Or/C? Not/C?
                                        Vectof? Vect/C? St/C? X/C? Hash/C? Set/C?
                                        ∀/C? Seal/C? -b?
                                        proc-arity-1?)]
              [(flat-contract?) (check-among -b? proc-arity-1?)]
              [(any/c)
               (match Vs
                 [(list (? Sealed?)) #f] ; know absolutely nothing about sealed
                 [_ '✓])]
              [(none/c) '✗]
              [(arity-includes?)
               (match Vs
                 [(list (-b (? Arity? a)) (-b (? Arity? b)))
                  (bool->Dec (arity-includes? a b))]
                 [_ #f])]
              [(immutable?)
               (define (check-at [α : α])
                 ((inst ⊔*/set V) (λ (V) (go 'immutable? (list V))) (Σᵥ@ Σ α)))
               (match (car Vs)
                 [(-b b) (bool->Dec (immutable? b))]
                 [(Hash^ _ _ im?) (bool->Dec im?)]
                 [(Set^ _ im?) (bool->Dec im?)]
                 [(X/G _ (or (? Hash/C?) (? Set/C?)) α) (check-at α)]
                 ;; No support for immutable vectors for now
                 [(or (? Vect?) (? Vect^?) (X/G _ (or (? Vect/C?) (? Vectof?)) _))
                  '✗]
                 [_ #f])])]
           [((P:¬ Q) _) (neg (go Q Vs))]
           [((P:≥ r) _) (go '>= (list (car Vs) (-b r)))]
           [((P:> r) _) (go '>  (list (car Vs) (-b r)))]
           [((P:≤ r) _) (go '<= (list (car Vs) (-b r)))]
           [((P:< r) _) (go '<  (list (car Vs) (-b r)))]
           [((P:≡ b) _) (go 'equal? (cons (-b b) Vs))]
           [(_ _) #f])]))
    (go P₀ Vs₀))

  (: ⊢@ : P (Listof S) → ?Dec)
  (define (⊢@ P Vs) ???)

  (: Ps⊢P : (℘ P) P → ?Dec)
  (define (Ps⊢P Ps P)
    (or (for/or : ?Dec ([Q (in-set Ps)]) (P⊢P Q P))
        (case P ;; Tmp. hack when `p` is implied by 2+ predicates
          [(exact-nonnegative-integer?)
           (cond [(and (∋ Ps 'exact-integer?)
                       (for/or : Boolean ([Q (in-set Ps)])
                         (match? Q
                                 (P:> (? (>/c -1)))
                                 (P:≥ (? (>=/c 0)))
                                 (P:≡ (? (>=/c 0))))))
                  '✓]
                 [(for/or : Boolean ([Q (in-set Ps)])
                    (match? Q
                            (P:< (? (<=/c 0)))
                            (P:≤ (? (</c 0)))
                            (P:≡ (? (</c 0)))))
                  '✗]
                 [else #f])]
          [(exact-positive-integer?)
           (cond [(and (∋ Ps 'exact-nonnegative-integer?)
                       (for/or : Boolean ([Q (in-set Ps)])
                         (match? Q
                                 (P:> (? (>=/c 0)))
                                 (P:≥ (? (>/c 0)))
                                 (P:≡ (? (>/c 0)))
                                 (P:¬ (P:≡ 0)))))
                  '✓]
                 [(and (∋ Ps 'exact-integer?)
                       (for/or : Boolean ([Q (in-set Ps)])
                         (match? Q
                                 (P:> (? (>=/c 0)))
                                 (P:≥ (? (>/c 0)))
                                 (P:≡ (? (>/c 0))))))
                  '✓]
                 [else #f])]
          [(any/c) '✓]
          [(none/c) '✗]
          [else #f])))

  (: P⊢P : P P → ?Dec)
  (splicing-local
      ((define (base-only? [P : P]) ; whether predicate only covers base types
         (and (symbol? P) (not (memq P '(list? struct?)))))
       (define (canon-P [P : P]) : P
         (case P
           [(positive?) (P:> 0)]
           [(negative?) (P:< 0)]
           [(zero?) (P:≡ 0)] ; FIXME no, subtlety with `0.0`
           [else P])))
    (define (P⊢P P Q)
      (match* ((canon-P P) (canon-P Q))
       ;; Base
       [(_ 'any/c) '✓]
       [('none/c _) '✓]
       [(_ 'none/c) '✗]
       [('any/c _) #f]
       [(P P) '✓]
       [((? symbol? P) (? symbol? Q)) (o⊢o P Q)]
       [(P 'values) (if (eq? P 'not) '✗ '✓)]
       [((-st-p 𝒾₁) (-st-p 𝒾₂)) (bool->Dec (𝒾₁ . substruct? . 𝒾₂))]
       [((? base-only?) (? -st-p?)) '✗]
       [((? -st-p?) (? base-only?)) '✗]
       ;; Negate
       [((P:¬ P) (P:¬ Q)) (and (eq? '✓ (P⊢P Q P)) '✓)]
       [(P (P:¬ Q)) (neg (P⊢P Q P))]
       [((P:¬ P) Q) (and (eq? '✓ (P⊢P Q P)) '✗)]
       ;; Special rules for real numbers
       ; < and <
       [((P:≤ a)              (P:< b)             ) (and     (<  a b) '✓)]
       [((or (P:< a) (P:≤ a)) (or (P:< b) (P:≤ b))) (and a b (<= a b) '✓)]
       ; > and >
       [((P:≥ a)              (P:> b)             ) (and     (>  a b) '✓)]
       [((or (P:> a) (P:≥ a)) (or (P:> b) (P:≥ b))) (and a b (>= a b) '✓)]
       ; < and >
       [((P:≤ a)              (P:≥ b)             ) (and     (<  a b) '✗)]
       [((or (P:< a) (P:≤ a)) (or (P:> b) (P:≥ b))) (and a b (<= a b) '✗)]
       ; > and <
       [((P:≥ a)              (P:≤ b)             ) (and (>  a b) '✗)]
       [((or (P:> a) (P:≥ a)) (or (P:< b) (P:≤ b))) (and a b (>= a b) '✗)]
       ; exact-nonnegative-integer?
       [('exact-nonnegative-integer? (P:< r)) (and (<= r 0) '✗)]
       [('exact-nonnegative-integer? (P:≤ r)) (and (<  r 0) '✗)]
       [('exact-nonnegative-integer? (P:> r)) (and (<  r 0) '✓)]
       [('exact-nonnegative-integer? (P:≥ r)) (and (<= r 0) '✓)]
       [((P:< r) 'exact-nonnegative-integer?) (and (<= r 0) '✗)]
       [((P:≤ r) 'exact-nonnegative-integer?) (and (<  r 0) '✗)]
       ; exact-positive-integer?
       [('exact-positive-integer? (P:< r)) (and (<  r 1) '✗)]
       [('exact-positive-integer? (P:≤ r)) (and (<  r 1) '✗)]
       [('exact-positive-integer? (P:> r)) (and (<  r 1) '✓)]
       [('exact-positive-integer? (P:≥ r)) (and (<= r 1) '✓)]
       [((P:< r) 'exact-positive-integer?) (and (<= r 1) '✗)]
       [((P:≤ r) 'exact-positive-integer?) (and (<  r 1) '✗)]
       ; _ -> real?
       [((or (? P:<?) (? P:≤?) (? P:>?) (? P:≥?)) (or 'real? 'number?)) '✓]
       [((P:≡ b) Q) (⊢@ Q (list (-b b)))]
       ; equal?
       [((P:≡ b₁) (P:≡ b₂)) (bool->Dec (equal? b₁ b₂))]
       [((P:< a) (P:≡ (? real? b))) #:when (<= a b) '✗]
       [((P:≤ a) (P:≡ (? real? b))) #:when (<  a b) '✗]
       [((P:> a) (P:≡ (? real? b))) #:when (>= a b) '✗]
       [((P:≥ a) (P:≡ (? real? b))) #:when (>  a b) '✗]
       [((P:≡ (? real? a)) (P:< b)) (bool->Dec (<  a b))]
       [((P:≡ (? real? a)) (P:≤ b)) (bool->Dec (<= a b))]
       [((P:≡ (? real? a)) (P:> b)) (bool->Dec (>  a b))]
       [((P:≡ (? real? a)) (P:≥ b)) (bool->Dec (>= a b))]
       ;; Default
       [(_ _) #f]))) 

  (splicing-local
      ((: with-conj : (Φ P (Listof S) → Φ) → Φ^ V W → Φ^)
       (define ((with-conj conj) Φ^₀ P W)
         (if (P? P)
             (let ([arg-lists (filter (λ ([Vs : (Listof V)]) (andmap S? Vs)) (cartesian W))])
               (for/set : Φ^ ([Φᵢ : Φ (in-set Φ^₀)])
                 (for/fold ([Φᵢ* : Φ Φᵢ]) ([Vs (in-list arg-lists)])
                   (conj Φᵢ* P Vs))))
             Φ^₀))
       (:* conj conj¬ : Φ P (Listof S) → Φ)
       (define (conj Φ P Vs)
         (match* (P Vs)
           [('values (list (S:@ P* Vs*))) (conj  Φ P* Vs*)]
           [('not    (list (S:@ P* Vs*))) (conj¬ Φ P* Vs*)]
           [(_       _                  ) (Φ+ Φ P Vs)]))
       (define (conj¬ Φ P Vs)
         (match* (P Vs)
           [('values (list (S:@ P* Vs*))) (conj¬ Φ P* Vs*)]
           [('not    (list (S:@ P* Vs*))) (conj  Φ P* Vs*)]
           [((P:< X) _                  ) (conj  Φ (P:≥ X) Vs)]
           [((P:≤ X) _                  ) (conj  Φ (P:> X) Vs)]
           [((P:> X) _                  ) (conj  Φ (P:≤ X) Vs)]
           [((P:≥ X) _                  ) (conj  Φ (P:< X) Vs)]
           [((P:¬ Q) _                  ) (conj  Φ Q Vs)]
           [(_       _                  ) (Φ+ Φ (P:¬ P) Vs)])))
    (define ∧ (with-conj conj))
    (define ∧¬ (with-conj conj¬)))

  (: Φ+ : Φ P (Listof S) → Φ)
  (define (Φ+ Φ Q Vs) (hash-update Φ Vs (λ ([Ps : (℘ P)]) (P+ Ps Q)) mk-∅))

  (: P+ : (℘ P) P → (℘ P))
  (define P+ #|TODO|# set-add)

  (splicing-let ([list-excl? ; TODO use prim-runtime
                  (set->predicate
                   {set 'number? 'integer? 'real? 'exact-nonnegative-integer?
                        'string? 'symbol?})])
    (: check-proper-list : Σ Φ V → ?Dec)
    (define (check-proper-list Σ Φ V₀)
      (define-set seen : α #:eq? #t #:as-mutable-hash? #t)

      (: go-α : α → ?Dec)
      (define (go-α α)
        (cond [(seen-has? α) '✓]
              [else (seen-add! α)
                    (⊔*/set go (Σᵥ@ Σ α))]))
      
      (: go : V → ?Dec)
      (define go
        (match-lambda
          [(Cons _ α) (go-α α)]
          [(Cons/G α) (go-α α)]
          [(-b b) (bool->Dec (null? b))]
          [(-● Ps) (cond [(∋ Ps 'list?) '✓]
                         [(sequence-ormap list-excl? Ps) '✗]
                         [else #f])]
          [(? S? S)
           (or (Ps⊢P (Φ@ Φ (list S)) 'list?)
               (match (Ps⊢P (Φ@ Φ (list S)) -cons?)
                 ['✓ (define S.cdr (S:@ -cdr (list S)))
                     (and (hash-has-key? Φ (list S.cdr)) (go S.cdr))]
                 [d d]))]))
      (go V₀)))

  (: check-one-of : V (Listof Base) → ?Dec)
  (define (check-one-of V bs)
    (match V
      [(-b b) (if (member b bs) '✓ '✗)]
      [(? -●?) #f]
      [_ '✗]))

  (define ⊢V : (V → ?Dec)
    (match-lambda
      [(-b b) (bool->Dec (and b #t))]
      [(-● Ps) (neg (Ps⊢P Ps 'not))]
      [(? S?) #f]
      [_ '✓]))

  (: check-range-in : -o P → ?Dec)
  (define (o . check-range-in . P)
    (match o
      [(? symbol? o) (P⊢P (get-conservative-range o) P)]
      [(-st-mk 𝒾) (P⊢P (-st-p 𝒾) P)]
      [(? -st-mut?) (P⊢P 'void? P)]
      [_ #f]))

  (: V-arity (case-> [(U Clo Case-Clo) → Arity]
                     [V → (Option Arity)]))
  (define V-arity
    (match-lambda
      [(Clo xs _ _) (shape xs)]
      [(Case-Clo cases) (normalize-arity (map V-arity cases))]
      [(Fn:● arity _) arity]
      [(or (And/C #t _ _) (Or/C #t _ _) (? Not/C?) (St/C #t _ _) (? One-Of/C?)) 1]
      [(X/G (? Fn/C? G) _ _) (guard-arity G)]
      [(? -st-p?) 1]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (prim-arity o)]
      [V
       #:when (not (or (Clo? V) (Case-Clo? V))) ; to convince TR
       (log-warning "Warning: call `V-arity` on an obviously non-procedure ~a" V)
       #f]))
  ) 

#|

(define-unit local-prover@
  (import static-info^ prims^ path^ sto^ val^ pretty-print^ sat-result^)
  (export local-prover^)

  ;; Check whether predicate excludes boolean
  (define boolean-excludes? (set->predicate (get-exclusions 'boolean?)))

  (: lift-p∋V : (-σ -φ -h -V * → -R) → -σ -φ -h -V^ * → -R)
  (define ((lift-p∋V p∋V₁) σ φ p . V^s)
    (let go ([V^s : (Listof -V^) V^s] [Vs-rev : (Listof -V) '()])
      (match V^s
        ['() (apply p∋V₁ σ φ p (reverse Vs-rev))]
        [(cons V^₁ V^s*)
         ((inst R⊔* -V) (λ (V) (go V^s* (cons V Vs-rev))) V^₁)]))) 

  (: p∋V : -σ -φ -h -V * → -R)
  (define (p∋V σ φ p . Vs)
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
      [(list (-St 𝒾 αs₁) (-St 𝒾 αs₂))
       #:when (equal? p 'equal?)
       (check-equal αs₁ αs₂)]
      
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
                      (-● (app set->list (list _ ... (or (-≥/c (-b (? real? b₂)))
                                                         (->/c (-b (? real? b₂)))) _ ...))))
                #:when (and b₂ (>= b₂ b₁))
                '✓]
               [(list (-b (? real? b₁))
                      (-● (app set->list (list _ ... (-</c (-b (? real? b₂))) _ ...))))
                #:when (and b₂ (<= b₂ b₁))
                '✗]
               [(list (-● ps) (-b (? real? b)))
                (match (set->list ps)
                  [(list _ ... (-</c (-b (? real? a))) _ ...) (if (<= a b) '✓ '?)]
                  [(list _ ... (-≤/c (-b (? real? a))) _ ...) (if (<= a b) '✓ '?)]
                  [(list _ ... (->/c (-b (? real? a))) _ ...) (if (>  a b) '✗ '?)]
                  [(list _ ... (-≥/c (-b (? real? a))) _ ...) (if (>  a b) '✗ '?)]
                  [(list _ ... (-≡/c (-b (? real? a))) _ ...) #:when a (if (<= a b) '✓ '✗)]
                  [_ '?])]
               [(list (-● ps) (and (? -t? t) (not (? -b?))))
                (cond [(∋ ps (-≤/c t)) '✓]
                      [(∋ ps (-</c t)) '✓]
                      [(∋ ps (->/c t)) '✗]
                      [else '?])]
               [(list (and (? -t? t) (not (? -b?))) (-● ps))
                (cond [(∋ ps (-≥/c t)) '✓]
                      [(∋ ps (->/c t)) '✓]
                      [(∋ ps (-</c t)) '✗]
                      [else '?])]
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
  )
|#
