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
  (import static-info^ meta-functions^
          sto^ evl^ val^ prims^
          sat-result^)
  (export local-prover-core^)
  (init-depend prims^)

  (: check : (U Σ Σᵥ) Φ T (Listof T) → ?Dec)
  (define (check Σ Φ P₀ Ts₀)
    
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

    (: go-harder : P S → ?Dec)
    (define (go-harder P S)
      (⊔*/set (λ ([V : V]) (go P (list V))) (T->V Σ {set Φ} S)))

    (: go : T (Listof T) → ?Dec)
    (define (go P Vs)
      (cond
        [(and (P? P)
              (andmap S? Vs)
              (or (Ps⊢P (Ψ@ Φ Vs) P)
                  (neg (Ps⊢P (Ψ@ Φ Vs) (P:¬ P)))))]
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
           [((or (? -st-mk?) (? -st-mut?)) _) '✓]
           [((-st-p 𝒾) Vs)
            (match Vs
              [(list (or (St 𝒾* _) (X/G _ (St/C _ 𝒾* _) _)))
               (bool->Dec (and 𝒾* (𝒾* . substruct? . 𝒾)))]
              [(list (? S? S)) (go-harder P S)]
              [_ '✗])]
           [((One-Of/C bs) _) (check-one-of (car Vs) bs)]
           [((? symbol?) _)
            (define-simple-macro (with-base-predicates ([g:id ... o?:id] ...)
                                   c ...)
              (case P
                [(o?)
                 (match Vs
                   [(list V)
                    (match V
                      [(-b (and b (? g) ...)) (bool->Dec (o? b))]
                      [(? S? S) (go-harder 'o? S)]
                      [_ '✗])]
                   [_ '✗])] ...
                c ...))
            (define (proc-arity-1? [T : T])
              (and (equal? '✓ (go 'procedure? (list T)))
                   (arity-includes? (assert (T-arity T)) 1)))
            (: check-among : (V → Boolean) * → ?Dec)
            (define (check-among . ps)
              (match Vs
                [(list V)
                 (or (for/or : (Option '✓) ([p (in-list ps)])
                       (and (if (S? V)
                                (set-andmap p (T->V Σ {set Φ} V))
                                (p V))
                            '✓))
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
                 [_ #f])]
              [(<=)
               (match Vs
                 [(list (-b (? real? x)) (-b (? real? y))) (bool->Dec (<= x y))]
                 [(list (-b (? real? x)) (-● Ps))
                  (for/or : ?Dec ([P (in-set Ps)])
                    (match P
                      [(or (P:≥ y) (P:> y)) #:when (and y (>= y x)) '✓]
                      [(P:< y) #:when (<= y x) '✗]
                      ['exact-nonnegative-integer? #:when (<= x 0) '✓]
                      ['exact-positive-integer? #:when (<= x 1) '✓]
                      [_ #f]))]
                 [(list (-● Ps) (-b (? real? y)))
                  (for/or : ?Dec ([P (in-set Ps)])
                    (match P
                      [(P:< x) (and (<= x y) '✓)]
                      [(P:≤ x) (and (<= x y) '✓)]
                      [(P:> x) (and (>  x y) '✗)]
                      [(P:≥ x) (and (>  x y) '✗)]
                      [(P:≡ (? real? x)) (bool->Dec (<= x y))]
                      [_ #f]))]
                 [_ #f])]
              [(<) (neg (go '<= (reverse Vs)))]
              [(>) (neg (go '<= Vs))]
              [(>=) (go '<= (reverse Vs))]
              [(= equal? eq? char=? string=?)
               (match Vs
                 [(list (-b x) (-b y)) (bool->Dec (equal? x y))]
                 [(list (-● Ps) (-b b)) (Ps⊢P Ps (P:≡ b))]
                 [(list (-b b) (-● Ps)) (Ps⊢P Ps (P:≡ b))]
                 [(list (? -o? o₁) (? -o? o₂)) (bool->Dec (equal? o₁ o₂))]
                 [_ #f])]
              [(list?) (check-proper-list Σ Φ (car Vs))]
              [(port? input-port? output-port?) '✗]
              [else (and (bool-excludes? (get-conservative-range P)) '✓)])]
           [((P:¬ Q) _) (neg (go Q Vs))]
           [((P:≥ r) _) (go '>= (list (car Vs) (-b r)))]
           [((P:> r) _) (go '>  (list (car Vs) (-b r)))]
           [((P:≤ r) _) (go '<= (list (car Vs) (-b r)))]
           [((P:< r) _) (go '<  (list (car Vs) (-b r)))]
           [((P:≡ b) _) (go 'equal? (cons (-b b) Vs))]
           [(_ _) #f])]))

    (go P₀ Ts₀))

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
       [((P:¬ P) (P:¬ Q)) (case (P⊢P Q P)
                            [(✓) '✓]
                            [else #f])]
       [(P (P:¬ Q)) (neg (P⊢P P Q))]
       [((P:¬ P) Q) (case (P⊢P Q P)
                      [(✓) '✗]
                      [else #f])]
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
       [((P:≡ b) Q) (check dummy-Σ ⊤Φ Q (list (-b b)))]
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
      ((: with-conj : (Φ P (Listof S) → Φ) → R T → R)
       (define ((with-conj conj) R₀ P)
         (cond
           [(P? P)
            (match-define (R W Φ^₀) R₀)
            (define Φ^₁ (cond [(andmap S? W)
                               (for/set : Φ^ ([Φ : Φ (in-set Φ^₀)])
                                 (conj Φ P W))]
                              [else Φ^₀]))
            (R W Φ^₁)]
           [else R₀]))
       (:* conj conj¬ : Φ P (Listof S) → Φ)
       (define (conj Φ P Vs)
         (match* (P Vs)
           [('values (list (S:@ (? -o? P*) Vs*))) (conj  Φ P* Vs*)]
           [('not    (list (S:@ (? -o? P*) Vs*))) (conj¬ Φ P* Vs*)]
           [(_       _                          ) (Φ+ Φ P Vs)]))
       (define (conj¬ Φ P Vs)
         (match* (P Vs)
           [('values (list (S:@ (? -o? P*) Vs*))) (conj¬ Φ P* Vs*)]
           [('not    (list (S:@ (? -o? P*) Vs*))) (conj  Φ P* Vs*)]
           [((P:< X) _                          ) (conj  Φ (P:≥ X) Vs)]
           [((P:≤ X) _                          ) (conj  Φ (P:> X) Vs)]
           [((P:> X) _                          ) (conj  Φ (P:≤ X) Vs)]
           [((P:≥ X) _                          ) (conj  Φ (P:< X) Vs)]
           [((P:¬ Q) _                          ) (conj  Φ Q Vs)]
           [(_       _                          ) (Φ+ Φ (P:¬ P) Vs)])))
    (define ∧ (with-conj conj))
    (define ∧¬ (with-conj conj¬)))

  (: Φ+ : Φ P (Listof S) → Φ)
  (define (Φ+ Φ₀ Q Vs)
    (match-define (Φ $ Ψ) Φ₀)
    (Φ $ (hash-update Ψ Vs (λ ([Ps : (℘ P)]) (P+ Ps Q)) mk-∅)))

  (: P+ : (℘ P) P → (℘ P))
  (define P+ #|TODO|# set-add)

  (splicing-let ([list-excl? ; TODO use prim-runtime
                  (set->predicate
                   {set 'number? 'integer? 'real? 'exact-nonnegative-integer?
                        'string? 'symbol?})])
    (: check-proper-list : (U Σ Σᵥ) Φ T → ?Dec)
    (define (check-proper-list Σ Φ T₀)
      (define Ψ (Φ-condition Φ))
      (define-set seen : α #:eq? #t #:as-mutable-hash? #t)

      (: go-α : α → ?Dec)
      (define (go-α α)
        (cond [(seen-has? α) '✓]
              [else (seen-add! α)
                    (⊔*/set go (Σᵥ@ Σ α))]))
      
      (: go : T → ?Dec)
      (define go
        (match-lambda
          [(Cons _ α) (go-α α)]
          [(Cons/G α) (go-α α)]
          [(-b b) (bool->Dec (null? b))]
          [(S:@ (== -cons) (list _ S)) (go S)]
          [(-● Ps) (cond [(∋ Ps 'list?) '✓]
                         [(sequence-ormap list-excl? Ps) '✗]
                         [else #f])]
          [(? S? S)
           (or (Ps⊢P (Ψ@ Φ (list S)) 'list?)
               (match (Ps⊢P (Ψ@ Φ (list S)) -cons?)
                 ['✓ (define S.cdr (S:@ -cdr (list S)))
                     (and (hash-has-key? Ψ (list S.cdr)) (go S.cdr))]
                 [d d]))]))
      (go T₀)))

  (: check-one-of : T (Listof Base) → ?Dec)
  (define (check-one-of T bs)
    (match T
      [(-b b) (if (member b bs) '✓ '✗)]
      [(? -●?) #f]
      [(? S?) #f]
      [_ '✗]))

  (define ⊢T : (T → ?Dec)
    (match-lambda
      [(-b b) (bool->Dec (and b #t))]
      [(-● Ps) (neg (Ps⊢P Ps 'not))]
      [(S:@ (? -st-mk?) _) '✓]
      [(? S?) #f]
      [_ '✓]))

  (: check-range-in : -o P → ?Dec)
  (define (o . check-range-in . P)
    (match o
      [(? symbol? o) (P⊢P (get-conservative-range o) P)]
      [(-st-mk 𝒾) (P⊢P (-st-p 𝒾) P)]
      [(? -st-mut?) (P⊢P 'void? P)]
      [_ #f]))

  (define bool-excludes? (set->predicate (get-exclusions 'boolean?)))

  (: T-arity (case-> [Clo → (U Natural arity-at-least)]
                     [Case-Clo → Arity]
                     [T → (Option Arity)]))
  (define T-arity
    (match-lambda
      [(Clo xs _ _) (shape xs)]
      [(Case-Clo cases) (normalize-arity (map T-arity cases))]
      [(-● Ps) (for/or : (Option Arity) ([P (in-set Ps)])
                 (match P
                   [(P:arity-includes a) a]
                   [_ #f]))]
      [(or (And/C #t _ _) (Or/C #t _ _) (? Not/C?) (St/C #t _ _) (? One-Of/C?)) 1]
      [(X/G _ (? Fn/C? G) α) (or (guard-arity G)
                                 (match-let ([(-α:fn _ _ a) (inspect-α α)])
                                   a))]
      [(? -st-p?) 1]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (prim-arity o)]
      [V
       #:when (not (or (Clo? V) (Case-Clo? V))) ; to convince TR
       (log-warning "Warning: call `T-arity` on non-procedure ~a" V)
       #f]))

  (: T->V : ((U Σ Σᵥ) Φ^ (U T T^) → V^))
  (define (T->V Σ Φ^ T)

    (: refine : V^ (℘ P) → V^)
    (define (refine Vs Ps)
      (for*/fold ([acc : V^ Vs])
                 ([P (in-set Ps)]
                  [Vᵢ (in-set Vs)]
                  #:when (for/and : Boolean ([Φ : Φ (in-set Φ^)])
                           (eq? '✗ (check Σ Φ P (list Vᵢ)))))
        (set-remove acc Vᵢ)))

    (define S->V : (S → V^)
      (match-lambda
        [(? -b? b) {set b}]
        [(? -o? o) {set o}]
        [(and S (S:α α)) (refine (Σᵥ@ Σ α) (Ψ@ Φ^ (list S)))]
        [(and S (S:@ Sₕ Sₓs)) {set (-● (Ψ@ Φ^ (list S)))}]))
    
    (cond [(S? T) (S->V T)]
          [(set? T) T]
          [else {set T}]))

  (: V^+ (case-> [V^ V → V^]
                 [T^ V → T^]))
  (define (V^+ x p)

    (define ?concretize : (V → (Option V^))
      (match-lambda
        ['null? {set -null}]
        ['not {set -ff}]
        [_ #f]))
    
    (define V+ : (V V → V)
      (match-lambda**
       [(V (St/C _ 𝒾 _)) (V+ V (-st-p 𝒾))]
       [(V (-st-p 𝒾)) #:when (zero? (count-struct-fields 𝒾)) (St 𝒾 '())]
       [((-● ps) (? P? p)) (-● (Ps+ ps p))]
       [(V _) V]))

    (cond [(?concretize p)]
          [(set? x)
           (for/fold ([acc : V^ ∅]) ([V (in-set x)])
             (case (check dummy-Σ ⊤Φ p (list V))
               [(✓) (set-add acc V)]
               [(✗) acc]
               [else (set-add acc (V+ V p))]))]
          [else x]))

  (define dummy-Σ (⊥Σ))
  ) 
