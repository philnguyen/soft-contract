#lang typed/racket/base

(provide prover@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/string
         racket/list
         racket/bool
         racket/vector
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-type S (U T -prim))

(define-unit prover@
  (import static-info^ meta-functions^
          sto^ val^
          prims^)
  (export prover^)

  (: sat : Σ V D * → ?Dec)
  (define (sat Σ P . Ds)
    (match Ds
      [(list D) (sat^₁ (λ (V) (sat₁ Σ P V)) D)]
      [(list D₁ D₂) (sat^₂ (λ (V₁ V₂) (sat₂ Σ P V₁ V₂)) D₁ D₂)]
      [_ #f]))

  (: Γ-sat? : Γ → Boolean)
  ;; Check if envronment/path-condition is satisfiable.
  ;; - `#f` means "definitely unsat"
  ;; - `#f` means "maybe sat"
  (define (Γ-sat? Γ)
    (define-values (eqs diseqs) (Γ->eqs/diseqs Γ))
    (sat/extra? eqs diseqs))

  (: maybe=? : Σ Integer D → Boolean)
  ;; Check if value `V` can possibly be integer `i`
  (define (maybe=? Σ i D)
    (if (set? D)
        (set-ormap (λ ([V : V]) (and (memq (sat₂ Σ 'equal? (-b i) V) '(✓ #f)) #t)) D)
        (and (memq (sat₂ Σ 'equal? (-b i) D) '(✓ #f)) #t)))

  (: check-plaus : Σ V W → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
  (define (check-plaus Σ P W)
    (match W
      [(list V    ) (distribute₁ Σ P V)]
      [(list V₁ V₂) (distribute₂ Σ P V₁ V₂)]
      [_ (let ([r (cons W ⊥ΔΣ)])
           (values r r))]))

  (: reify : (℘ P) → V^)
  (define (reify Ps)
    (cond [(set-ormap ?concretize Ps) => values]
          [(∋ Ps (P:¬ 'values)) {set -ff}]
          [(and (∋ Ps 'values) (∋ Ps 'boolean?)) {set -tt}]
          [else {set (-● (set-filter P? Ps))}]))
  
  (: ?concretize : P → (Option V^))
  (define ?concretize
    (match-lambda
      ['null? {set -null}]
      ['not {set -ff}]
      ['set-empty? {set (Empty-Set)}]
      ['hash-empty? {set (Empty-Hash)}]
      ['void? {set -void}]
      ;[(-st-p 𝒾) #:when (zero? (count-struct-fields 𝒾)) {set (St 𝒾 '() ∅)}]
      [(P:≡ b) {set (-b b)}]
      [_ #f]))

  (: refine : D (U V (℘ P)) Σ → (Values D ΔΣ))
  (define (refine D₀ P* Σ)
    (cond
      [(set? D₀) (values (refine-V^ D₀ P* Σ) ⊥ΔΣ)]
      [(-prim? D₀) (values D₀ ⊥ΔΣ)]
      [else
       (values D₀
               (if (set? P*)
                   (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([P (in-set P*)])
                     (⧺ ΔΣ (refine-T D₀ P Σ)))
                   (refine-T D₀ P* Σ)))]))

  (: refine-not : D V Σ → (Values D ΔΣ))
  (define (refine-not D P Σ)
    (cond [(set? D) (values (refine-not-V^ D P Σ) ⊥ΔΣ)]
          [(-prim? D) (values D ⊥ΔΣ)]
          [else (values D (refine-not-T D P Σ))]))

  (: refine₁ : D¹ V Σ → (Values D ΔΣ))
  (define (refine₁ V P Σ)
    (cond [(or (-●? V) (St? V)) (values (refine-V V P Σ) ⊥ΔΣ)]
          [(T? V) (values V (refine-T V P Σ))]
          [else (values {set V} ⊥ΔΣ)]))

  (define ?negate : (P → (Option P))
    (match-lambda
      [(P:¬ Q) Q]
      [(P:St ac P) (match (?negate P)
                     [(? values P*) (P:St ac P*)]
                     [_ #f])]
      [(? Q? Q) (P:¬ Q)]
      [_ #f]))

  (:* refine-V-V refine-not-V-V : V V V Σ → (Values V^ V^))
  ;; TODO
  (define (refine-V-V V₁ V₂ P Σ) (values {set V₁} {set V₂}))
  (define (refine-not-V-V V₁ V₂ P Σ) (values {set V₂} {set V₂}))

  (:* refine-V-T refine-not-V-T : V S V Σ → (Values V^ ΔΣ))
  ;; TODO
  (define (refine-V-T V T P Σ) (values {set V} (if (-b? V) (refine-T-T V T P Σ) ⊥ΔΣ)))
  (define (refine-not-V-T V T P Σ) (values {set V} (if (-b? V) (refine-not-T-T V T P Σ) ⊥ΔΣ)))

  (:* refine-T-V refine-not-T-V : S V V Σ → (Values ΔΣ V^))
  ;; TODO
  (define (refine-T-V T V P Σ) (values (if (-b? V) (refine-T-T T V P Σ) ⊥ΔΣ) {set V}))
  (define (refine-not-T-V T V P Σ) (values (if (-b? V) (refine-not-T-T T V P Σ) ⊥ΔΣ) {set V}))

  (:* refine-T-T refine-not-T-T : S S V Σ → ΔΣ)
  (splicing-local
      ((: refine-both (∀ (X) (Base → Boolean : X) K -b S (X → P) S (X → P) Σ → ΔΣ))
       (define (refine-both ub? P b V₁ P₁ V₂ P₂ Σ)
         (match* (V₁ V₂)
           [((? T? V₁) (? T? V₂))
            (define T-prop (T:@ P (list V₁ V₂)))
            ((inst cons ΔΞ ΔΓ) ⊥Ξ (hash T-prop b))]
           [((? T? V₁) (-b (? ub? u₂)))
            (refine-T V₁ (P₁ u₂) Σ)]
           [((-b (? ub? u₁)) (? T? V₂))
            (refine-T V₂ (P₂ u₁) Σ)]
           [(_ _) ⊥ΔΣ])))
    (define (refine-T-T T₁ T₂ P Σ)
      (case P
        [(< ) (refine-both real? (K:≤) -ff T₂ P:> T₁ P:< Σ)] ; V₁ < V₂ ⇔ ¬ (V₁ ≥ V₂) ⇔ ¬ (V₂ ≤ V₁)
        [(<=) (refine-both real? (K:≤) -tt T₁ P:≤ T₂ P:≥ Σ)]
        [(> ) (refine-both real? (K:≤) -ff T₁ P:> T₂ P:< Σ)] ; V₁ > V₂ ⇔ ¬ (V₁ ≤ V₂)
        [(>=) (refine-both real? (K:≤) -tt T₂ P:≤ T₁ P:≥ Σ)]
        [(= ) (refine-both number? (K:=) -tt T₁ P:= T₂ P:= Σ)]
        [(equal? eq? eqv? char=? string=?)
         (refine-both base? (K:≡) -tt T₁ P:≡ T₂ P:≡ Σ)]
        [else ⊥ΔΣ]))
    (define (refine-not-T-T T₁ T₂ P Σ)
      (define (go [P : Symbol]) (refine-T-T T₁ T₂ P Σ))
      (case P
        [(< ) (go '>=)]
        [(<=) (go '> )]
        [(> ) (go '<=)]
        [(>=) (go '< )]
        [(=)
         (define P:≠ (compose P:¬ P:=))
         (refine-both number? (K:=) -ff T₁ P:≠ T₂ P:≠ Σ)]
        [(equal? eq? eqv? char=? string=?)
         (define P:≢ (compose P:¬ P:≡))
         (refine-both base? (K:≡) -ff T₁ P:≢ T₂ P:≢ Σ)]
        [else ⊥ΔΣ])))

  (: refine-Ps : (℘ P) V → (℘ P))
  ;; Strengthen refinement set with new predicate
  (define (refine-Ps Ps₀ P₀)
    ;; Combine 2 predicates for a more precise one.
    ;; Return `#f` if there's no single predicate that refines both
    (define P+ : (P P → (Option (Listof P)))
      (match-lambda**/symmetry
       [(P Q) #:when (equal? '✓ (P⊢P P Q)) (list P)]
       [((or 'exact-integer? 'exact-nonnegative-integer?)
         (P:≥ (and (? (between/c 0 1)) (not 0))))
        (list 'exact-positive-integer?)]
       [((or 'exact-integer? 'exact-nonnegative-integer?)
         (P:> (and (? (between/c 0 1)) (not 1))))
        (list 'exact-positive-integer?)]
       [('exact-integer? (P:≥ (and (? (between/c -1 0)) (not -1))))
        (list 'exact-nonnegative-integer?)]
       [('exact-integer? (P:> (and (? (between/c -1 0)) (not 0))))
        (list 'exact-nonnegative-integer?)]
       [((or 'exact-integer? 'exact-nonnegative-integer?) 'zero?)
        (list (P:≡ 0))]
       [('exact-nonnegative-integer? (or (P:¬ (or 'zero? (P:= 0) (P:≤ 0)))
                                         (P:> 0)))
        (list 'exact-positive-integer?)]
       [('list? (P:¬ 'null?)) (list 'list? -cons?)]
       [('list? (P:¬ -cons?)) (list 'null?)]
       [((and P (or (? P:>?) (? P:≥?) (? P:<?) (? P:≤?))) 'number?)
        (list P 'real?)]
       #:else
       [(P₀ Q₀)
        (match* (P₀ Q₀)
          [((P:St ac P*) (P:St ac Q*))
           (match (P+ P* Q*)
             [(? values Ps) (map (λ ([P : P]) (P:St ac P)) Ps)]
             [_ #f])]
          [(_ _) #f])]))
    (if (P? P₀) (merge/compact P+ P₀ Ps₀) Ps₀))

  (: sat₁ : Σ V D¹ → ?Dec)
  (define (sat₁ Σ P V₀)
    (cond
      [(-●? V₀) (Ps⊢P (-●-_0 V₀) P)]
      [(T:@? V₀)
       (define k (T:@-_0 V₀))
       (or (and (symbol? k) (P⊢P (get-conservative-range k) P))
           (sat^₁ (λ (V) (sat₁ Σ P V)) (unpack V₀ Σ)))]
      [(γ? V₀) (sat^₁ (λ (V) (sat₁ Σ P V)) (unpack V₀ Σ))]
      [else
       (match P
         [(-st-p 𝒾)
          (match V₀
            [(or (St (α:dyn (β:st-elems _ 𝒾*) _) _)
                 (Guarded _ (? St/C? (app St/C-tag 𝒾*)) _))
             (bool->Dec (and 𝒾* (𝒾* . substruct? . 𝒾)))]
            [_ '✗])]
         [(One-Of/C bs) (bool->Dec (and (-b? V₀) (∋ bs (-b-unboxed V₀))))]
         [(P:St (-st-ac 𝒾 i) P*)
          (match V₀
            [(St α Ps)
             (or (Ps⊢P Ps P)
                 (sat^₁ (λ (Vᵢ) (sat₁ Σ P* Vᵢ)) (vector-ref (Σ@/blob α Σ) i)))]
            [(? -●?) !!!]
            [_ '✗])]
         [(P:¬ Q) (neg (sat₁ Σ Q V₀))]
         [(P:≥ b) (sat₂ Σ '>= V₀ (-b b))]
         [(P:> b) (sat₂ Σ '>  V₀ (-b b))]
         [(P:≤ b) (sat₂ Σ '<= V₀ (-b b))]
         [(P:< b) (sat₂ Σ '<  V₀ (-b b))]
         [(P:= b) (sat₂ Σ '=  V₀ (-b b))]
         [(P:≡ b) (sat₂ Σ 'equal? V₀ (-b b))]
         [(P:arity-includes a)
          (match (arity V₀)
            [(? values V₀:a) (bool->Dec (arity-includes? V₀:a a))]
            [#f '✗])]
         [(P:vec-len n)
          (match V₀
            [(Vect (α:dyn (β:vect-elems _ m) _)) (bool->Dec (= n m))]
            [(Vect-Of _ Vₙ) (sat^₂ (λ (V₁ V₂) (sat₂ Σ '= V₁ V₂)) {set (-b n)} Vₙ)]
            [(Guarded _ G _)
             (match G
               [(? Vect/C?) (define-values (_₁ _₂ m) (Vect/C-fields G))
                            (bool->Dec (= n m))]
               [(Vectof/C _ _) #f]
               [_ '✗])]
            [_ '✗])]
         [(? symbol?)
          (define-simple-macro (with-base-predicates ([g:id ... o?] ...)
                                 c ...)
            (case P
              [(o?) (bool->Dec (and (-b? V₀) (let ([V* (-b-unboxed V₀)])
                                               (and (g V*) ... (o? V*)))))]
              ...
              c ...))
          (: check-among : (V → Boolean) * → ?Dec)
          (define (check-among . ps)
            (or (for/or : (Option '✓) ([p (in-list ps)] #:when (p V₀)) '✓) '✗))
          (: with-guard : (V → Boolean) * → (V → Boolean))
          (define (with-guard . ps)
            (match-lambda [(Guarded _ G _)
                           (for/or : Boolean ([p? (in-list ps)]) (p? G))]
                          [_ #f]))
          (: proper-flat-contract? : V → Boolean)
          (define proper-flat-contract?
            (match-lambda
              [(-st-mk 𝒾) (= 1 (count-struct-fields 𝒾))]
              [(or (? -st-p?) (? -st-ac?)) #t]
              [(? symbol? o) (arity-includes? (prim-arity o) 1)]
              [(? Not/C?) #t]
              [(? One-Of/C?) #t]
              [(and C (or (? And/C?) (? Or/C?) (? St/C?))) (C-flat? C Σ)]
              [(Clo xs _ _) (arity-includes? (shape xs) 1)]
              [(-λ xs _ _) (arity-includes? (shape xs) 1)]
              [(Case-Clo clos _) (ormap proper-flat-contract? clos)]
              [(Guarded _ (? Fn/C? C) _) (arity-includes? (guard-arity C) 1)]
              [_ #f]))
          ;; Order matters. More specific ones come first.
          (with-base-predicates ([not]
                                 [byte?]
                                 [fixnum?]
                                 [exact-positive-integer?]
                                 [exact-nonnegative-integer?]
                                 [exact-integer? even?]
                                 [exact-integer? odd?]
                                 [exact-integer?]
                                 [real? positive?]
                                 [real? negative?]
                                 [number? zero?]
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
            [(values) (bool->Dec (or (not (-b? V₀)) (not (not (-b-unboxed V₀)))))]
            [(procedure?) ; FIXME make sure `and/c` and friends are flat
             (check-among -o? Fn? (with-guard Fn/C?) proper-flat-contract?)]
            [(vector?)
             (check-among Vect? Vect-Of? (with-guard Vect/C? Vectof/C?))]
            [(hash-empty?)
             (match V₀
               [(Empty-Hash) '✓]
               [(Guarded _ (? Hash/C?) _) #f]
               [_ '✗])]
            [(hash?) (check-among Empty-Hash? Hash-Of? (with-guard Hash/C?))]
            [(set? generic-set?) (check-among Empty-Set? Set-Of? (with-guard Set/C?))]
            [(set-empty?)
             (match V₀
               [(Empty-Set) '✓]
               [(Guarded _ (? Set/C?) _) #f]
               [_ '✗])]
            [(contract?)
             (check-among Fn/C? And/C? Or/C? Not/C? Rec/C?
                          Vectof/C? Vect/C? St/C? Hash/C? Set/C? proper-flat-contract?
                          ∀/C? Seal/C? -b?)]
            [(flat-contract?) (check-among -b? proper-flat-contract?)]
            ;; Take more conservative view of sealed value than standard Racket.
            ;; `sealed` is the lack of type information.
            ;; Can't assume a sealed value is `any/c`,
            ;; even when it's the top of the only type hierarchy there is.
            ;; This prevents sealed values from being inspected even by
            ;; "total" predicates and ensures that codes with and without
            ;; parametric contracts behave the same.
            [(any/c) (if (Sealed? V₀) #f '✓)]
            [(none/c) '✗]
            [(immutable?)
             (define go : (D¹ → ?Dec)
               (match-lambda
                 [(-b b) (bool->Dec (immutable? b))]
                 [(or (? Empty-Hash?) (? Hash-Of?) (? Empty-Set?) (? Set-Of?)) '✓]
                 [(Guarded _ (or (? Hash/C?) (? Set/C?)) α) (go-α α)]
                 [(or (? Vect?) (? Vect-Of?) (Guarded _ (or (? Vect/C?) (? Vectof/C?)) _)) '✗]
                 [(-● Ps) (Ps⊢P Ps 'immutable?)]
                 [_ #f]))
             (: go-α : α → ?Dec)
             (define (go-α α) (sat^₁ go (unpack (Σ@ α Σ) Σ)))
             (go V₀)]
            [(list?) (check-proper-list Σ V₀)]
            [(port? input-port? output-port?) '✗] ; ports can't reach here
            [else (and (bool-excludes? (get-conservative-range P)) '✓)])]
         [_ #f])]))

  (: sat₂ : Σ V D¹ D¹ → ?Dec)
  (define (sat₂ Σ P V₁ V₂)
    (define (go [V₁ : D¹] [V₂ : D¹]) : ?Dec
      (case P
        [(equal? eq? char=? string=?) (check-equal? Σ V₁ V₂)]
        [(=) (check-= Σ V₁ V₂)]
        [(<=) (check-≤ Σ V₁ V₂)]
        [(<) (neg (check-≤ Σ V₂ V₁))]
        [(>=) (check-≤ Σ V₂ V₁)]
        [(>) (neg (check-≤ Σ V₁ V₂))]
        [(arity-includes?)
         (match* (V₁ V₂)
           [((-b (? Arity? a)) (-b (? Arity? b))) (bool->Dec (arity-includes? a b))]
           [(_ _) #f])]
        [else #f]))
    (cond [(go V₁ V₂) => values]
          [(and (T? V₁) (-b? V₂)) (sat^₂ go (unpack V₁ Σ) V₂)]
          [(and (-b? V₁) (T? V₂)) (sat^₂ go V₁ (unpack V₂ Σ))]
          [(and (T? V₁) (T? V₂)) (or (sat^₂ go (unpack V₁ Σ) V₂)
                                     (sat^₂ go V₁ (unpack V₂ Σ))
                                     (sat^₂ go (unpack V₁ Σ) (unpack V₂ Σ)))]
          [else #f]))

  (: check-= : Σ D¹ D¹ → ?Dec)
  (define (check-= Σ V₁ V₂)
    (: check-Ps-= : (℘ P) Real → ?Dec)
    (define (check-Ps-= Ps x)
      (define check-P : (P → ?Dec)
        (match-lambda
          ['exact-nonnegative-integer? (if (< x 0) '✗ #f)]
          ['exact-positive-integer? (if (< x 1) '✗ #f)]
          ['zero? (bool->Dec (= x 0))]
          [(or (P:= (? real? y))
               (P:≡ (? real? y)))
           (bool->Dec (= x (assert y)))]
          [(P:¬ (P:= (== x))) '✗]
          [_ #f]))
      (set-ormap check-P Ps))
    (match* (V₁ V₂)
      [((-b (? real? x)) (-b (? real? y))) (bool->Dec (= x y))]
      [((-● Ps) (-b (? real? x))) (check-Ps-= Ps x)]
      [((-b (? real? x)) (-● Ps)) (check-Ps-= Ps x)]
      [(_ _) (check-equal? Σ V₁ V₂)]))

  (: check-≤ : Σ D¹ D¹ → ?Dec)
  (define (check-≤ Σ V₁ V₂)
    (match* (V₁ V₂)
      [((-b (? real? x)) (-b (? real? y))) (bool->Dec (<= x y))]
      [((-b (? real? x)) (-● Ps))
       (for/or : ?Dec ([P (in-set Ps)])
         (match P
           [(or (P:≥ y) (P:> y)) #:when (and y (>= y x)) '✓]
           [(P:< y) #:when (<= y x) '✗]
           ['exact-nonnegative-integer? #:when (<= x 0) '✓]
           ['exact-positive-integer? #:when (<= x 1) '✓]
           [_ #f]))]
      [((-● Ps) (-b (? real? y)))
       (for/or : ?Dec ([P (in-set Ps)])
         (match P
           [(P:< x) (and (<= x y) '✓)]
           [(P:≤ x) (and (<= x y) '✓)]
           [(P:> x) (and (>= x y) '✗)]
           [(P:≥ x) (and (>  x y) '✗)]
           [(P:= (? real? x)) (bool->Dec (<= x y))]
           ['exact-nonnegaive-integer? #:when (< y 0) '✗]
           ['exact-positive-integer? #:when (< y 1) '✗]
           [_ #f]))]
      ;; More special cases to avoid SMT
      [((T:@ 'sub1 (list T)) T) '✓]
      [(T (T:@ 'sub1 (list T))) '✗]
      [((T:@ '- (list T (-b (? (>=/c 0))))) T) '✓]
      [(T (T:@ '- (list T (-b (? (>/c 0)))))) '✗]
      [((T:@ '+ (list T (-b (? (<=/c 0))))) T) '✓]
      [((T:@ '+ (list (-b (? (<=/c 0))) T)) T) '✓]
      [(T (T:@ '+ (list T (-b (? (</c 0)))))) '✗]
      [(T (T:@ '+ (list (-b (? (</c 0))) T))) '✗]
      [((and T₁ (or (? -b?) (? T?))) (and T₂ (or (? -b?) (? T?))))
       (match (hash-ref (cdr Σ) (T:@ (K:≤) (list T₁ T₂)) #f)
         [(-b b) (if b '✓ '✗)]
         [_
          (match (hash-ref (cdr Σ) (T:@ (K:≤) (list T₂ T₁)) #f)
            [(-b #f) '✓]
            [_ #f])])]
      [(_ _) #f]))

  (: check-equal? : Σ D¹ D¹ → ?Dec)
  (define (check-equal? Σ V₁ V₂)
    (: singleton-pred : (℘ P) → (Option P))
    (define (singleton-pred Ps)
      (for/or : (Option P) ([P (in-set Ps)] #:when (?concretize P))
        P))

    (: go-V^ : V^ V^ → ?Dec)
    (define (go-V^ Vs₁ Vs₂) (sat^₂ go-V Vs₁ Vs₂))

    (define-set seen : (Pairof α α) #:mutable? #t)
    (: go-blob : α α → ?Dec)
    (define (go-blob α₁ α₂)
      (define k (cons α₁ α₂))
      (cond [(seen-has? k) '✓]
            [else
             (seen-add! k)
             (for/fold ([acc : ?Dec '✓])
                       ([Vs₁ (in-vector (Σ@/blob α₁ Σ))]
                        [Vs₂ (in-vector (Σ@/blob α₂ Σ))]
                        #:break (eq? acc '✗))
               (case (go-V^ Vs₁ Vs₂)
                 [(✓) acc]
                 [(✗) '✗]
                 [(#f) #f]))]))

    (: go-V : D¹ D¹ → ?Dec)
    (define go-V
      (match-lambda**
       [((? -prim? x) (? -prim? y)) (bool->Dec (equal? x y))]
       [((-● Ps) (-b b)) (Ps⊢P Ps (P:≡ b))]
       [((-b b) (-● Ps)) (Ps⊢P Ps (P:≡ b))]
       [((? -prim?) (not (or (? -●?) (? T?) (? -prim?)))) '✗]
       [((-● Ps) (-● Qs))
        (match* ((singleton-pred Ps) (singleton-pred Qs))
          [(#f _) #f]
          [(_ #f) #f]
          [(P Q) (bool->Dec (equal? P Q))])]
       [((not (or (? -●?) (? T?) (? -prim?))) (? -prim?)) '✗]
       [((St (and α₁ (α:dyn (β:st-elems _ 𝒾₁) _)) _)
         (St (and α₂ (α:dyn (β:st-elems _ 𝒾₂) _)) _))
        (and (equal? 𝒾₁ 𝒾₂) (go-blob α₁ α₂))]
       [((T:@ o (list T₁ (T:@ o (list T₂ T₃))))
         (T:@ o (list (T:@ o (list T₁ T₂)) T₃)))
        #:when (memq o '(+ *)) '✓]
       [((T:@ o (list (T:@ o (list T₁ T₂)) T₃))
         (T:@ o (list T₁ (T:@ o (list T₂ T₃)))))
        #:when (memq o '(+ *)) '✓]
       [((? T? T₁) (? T? T₂)) (check-equal?/congruence (cdr Σ) T₁ T₂)]
       [((? T? T) (? V? V)) (go-V^ (unpack T Σ) {set V})]
       [((? V? V) (? T? T)) (go-V^ {set V} (unpack T Σ))]
       [(_ _) #f]))

    (go-V V₁ V₂))

  (: check-equal?/congruence : Γ S S → ?Dec)
  (define (check-equal?/congruence Γ T₁ T₂)
    (define-values (eqs diseqs) (Γ->eqs/diseqs Γ))
    (cond [(not (sat/extra? eqs (cons (cons T₁ T₂) diseqs))) '✓]
          [(not (sat/extra? (cons (cons T₁ T₂) eqs) diseqs)) '✗]
          [else #f]))

  (: Γ->eqs/diseqs : Γ → (Values (Listof (Pairof S S)) (Listof (Pairof S S))))
  (define (Γ->eqs/diseqs Γ)
    (for/fold ([eqs : (Listof (Pairof S S)) '()]
               [diseqs : (Listof (Pairof S S)) (list (cons -tt -ff))])
              ([(T D) (in-hash Γ)])
      (match* (T D)
        [((T:@ (K:≡) (list T₁ T₂)) (-b b))
         (if b
             (values (cons (cons T₁ T₂) eqs) diseqs)
             (values eqs (cons (cons T₁ T₂) diseqs)))]
        [(_ (or (? -b? T*) (? T? T*) {singleton-set (? -b? T*)}))
         (values (cons (cons T (assert T*)) eqs) diseqs)]
        [(_ _) (values eqs diseqs)])))

  (:* Ps⊢P simple-Ps⊢P : (℘ P) V → ?Dec)
  (define (Ps⊢P Ps Q)
    (define Q* (canonicalize Q))
    (if (set? Q*)
        (summarize-conj (map/set (λ ([Q : P]) (simple-Ps⊢P Ps Q)) Q*))
        (simple-Ps⊢P Ps Q*)))
  (define (simple-Ps⊢P Ps Q)
    (cond [(∋ Ps Q) '✓]
          [(and (equal? Q -cons?) (∋ Ps (P:¬ 'null?)) (∋ Ps 'list?)) '✓]
          [(and (memq Q '(exact-positive-integer? exact-nonnegative-integer?))
                (∋ Ps 'positive?)
                (∋ Ps 'byte?)) '✓]
          [(equal? Q 'none/c) '✗]
          [(equal? Q 'any/c) '✓]
          [else (for/or : ?Dec ([P (in-set Ps)]) (P⊢P P Q))]))

  (:* P⊢P simple-P⊢P : V V → ?Dec)
  (define (P⊢P P₀ Q₀)
    (define P* (canonicalize P₀))
    (define Q* (canonicalize Q₀))
    (cond [(and (set? P*) (set? Q*))
           (summarize-conj (map/set (λ ([Q : P]) (simple-Ps⊢P P* Q)) Q*))]
          [(set? Q*)
           (summarize-conj (map/set (λ ([Q : P]) (simple-P⊢P P* Q)) Q*))]
          [(set? P*) (simple-Ps⊢P P* Q*)]
          [else (simple-P⊢P P* Q*)]))
  (define (simple-P⊢P P Q)
    (match* (P Q)
      ;; Base
      [(_ 'any/c) '✓]
      [('none/c _) '✓]
      [(_ 'none/c) '✗]
      [('any/c _) #f]
      [(P P) '✓]
      [((P:St ac P*) (P:St ac Q*)) (simple-P⊢P P* Q*)]
      [((? symbol? P) (? symbol? Q)) (o⊢o P Q)]
      [((? -o? P) 'values) (match P ; TODO generalize
                             ['not '✗]
                             [_ #|TODO careful|# '✓])]
      [((-st-p 𝒾₁) (-st-p 𝒾₂)) (bool->Dec (𝒾₁ . substruct? . 𝒾₂))]
      [((? base-only?) (? -st-p?)) '✗]
      [((? -st-p?) (? base-only?)) '✗]
      [((One-Of/C bs) (P:≡ b))
       (if (∋ bs b)
           (if (> (set-count bs) 1) #f '✓)
           '✗)]
      [((P:≡ b) (One-Of/C bs)) (bool->Dec (∋ bs b))]
      [((P:≡ _) (or (? -st-p?) 'vector? 'set? 'hash?)) '✗]
      [((or (? -st-p?) 'vector? 'set? 'hash?) (P:≡ _)) '✗]
      [((or (? P:>?) (? P:≥?) (? P:<?) (? P:≤?) (? P:=?)) (or 'number? 'real?)) '✓]
      ;; Negate
      [((P:¬ P) (P:¬ Q)) (case (simple-P⊢P Q P)
                           [(✓) '✓]
                           [else #f])]
      [(P (P:¬ Q)) (neg (simple-P⊢P P Q))]
      [((P:¬ P) Q) (case (simple-P⊢P Q P)
                     [(✓) '✗]
                     [else #f])]
      ;; Special rules for numbers
      ; < and <
      [((P:≤ a) (P:< b))
       (and (<  a b) '✓)]
      [((or (P:< a) (P:≤ a))
        (or (P:< b) (P:≤ b)))
       (and a b (<= a b) '✓)]
      ; > and >
      [((P:≥ a) (P:> b))
       (and (>  a b) '✓)]
      [((or (P:> a) (P:≥ a))
        (or (P:> b) (P:≥ b)))
       (and a b (>= a b) '✓)]
      ; < and >
      [((P:≤ a) (P:≥ b))
       (and (<  a b) '✗)]
      [((or (P:< a) (P:≤ a))
        (or (P:> b) (P:≥ b)))
       (and a b (<= a b) '✗)]
      ; > and <
      [((P:≥ a) (P:≤ b))
       (and (>  a b) '✗)]
      [((or (P:> a) (P:≥ a))
        (or (P:< b) (P:≤ b)))
       (and a b (>= a b) '✗)]
      ; _ -> real?
      ;; `(P T)` subsuming `real?` causes problem when `(P T)` gets dropped
      ;; due to `T` going out of scope
      #;[((or (? P:<?) (? P:≤?) (? P:>?) (? P:≥?) (? P:=?)) (or 'real? 'number?)) '✓]
      [((P:= b) Q) (sat₁ ⊥Σ Q (-b b))]
      ; equal?
      [((P:= x) (P:= y)) (bool->Dec (= x y))]
      [((P:< a) (P:= (? real? b))) #:when (<= a b) '✗]
      [((P:≤ a) (P:= (? real? b))) #:when (<  a b) '✗]
      [((P:> a) (P:= (? real? b))) #:when (>= a b) '✗]
      [((P:≥ a) (P:= (? real? b))) #:when (>  a b) '✗]
      [((P:= (? real? a)) (P:< b)) (bool->Dec (<  a b))]
      [((P:= (? real? a)) (P:≤ b)) (bool->Dec (<= a b))]
      [((P:= (? real? a)) (P:> b)) (bool->Dec (>  a b))]
      [((P:= (? real? a)) (P:≥ b)) (bool->Dec (>= a b))]
      ;; Exclusion
      [((P:≤ T) (P:> T)) '✗]
      [((P:< T) (P:≥ T)) '✗]
      [((P:≥ T) (P:< T)) '✗]
      [((P:> T) (P:≤ T)) '✗]
      [((P:< T) (P:≤ T)) '✓]
      [((P:> T) (P:≥ T)) '✓]
      ;; Arities
      [((P:arity-includes a₁) (P:arity-includes a₂))
       (bool->Dec (arity-includes? a₁ a₂))]
      ;; Default
      [(_ _) #f]))

  ;; Whether predicate `P` only covers base types
  (define (base-only? [P : V])
    (and (symbol? P) (not (memq P '(list? struct?)))))
  
  (: bool->Dec : Boolean → Dec)
  (define (bool->Dec b) (if b '✓ '✗))

  (: neg : ?Dec → ?Dec)
  (define (neg d)
    (case d
      [(✓) '✗]
      [(✗) '✓]
      [else #f]))

  (: canonicalize : V → (U V (℘ P)))
  (define canonicalize
    (match-lambda
      ['exact-nonnegative-integer? {set 'exact? 'integer? (P:≥ 0)}]
      ['exact-positive-integer? {set 'exact? 'integer? (P:> 0)}]
      ['exact-integer? {set 'exact? 'integer?}]
      ['positive? (P:> 0)]
      ['negative? (P:< 0)]
      ['zero? (P:= 0)]
      ['index? {set 'fixnum? (P:≥ 0)}]
      [(P:¬ 'even?) 'odd?]
      [(P:¬ 'odd?) 'even?]
      [(and P₀ (P:St ac P*))
       (define P** (canonicalize P*))
       (cond [(eq? P** P*) P₀] ; try to re-use old instance
             [(set? P**) (map/set (λ ([P : P]) (P:St ac P)) P**)]
             [(P? P**) (P:St ac P**)]
             [else P₀])]
      [P P]))

  (splicing-let ([list-excl? ; TODO use prim-runtime
                  (set->predicate
                   {set 'number? 'integer? 'real? 'exact-nonnegative-integer?
                        'string? 'symbol?})])
    (: check-proper-list : Σ V → ?Dec)
    (define (check-proper-list Σ V₀)
      (define-set seen : α #:mutable? #t)

      (: go-α : α → ?Dec)
      (define (go-α α)
        (cond [(seen-has? α) '✓]
              [else (seen-add! α)
                    (match (Σ@/raw α Σ)
                      [(vector _ V) (go* V)]
                      [(? set? V) (go* V)])]))

      (: go* : V^ → ?Dec)
      (define (go* Vs)
        (summarize-disj
         (for/fold ([acc : (℘ ?Dec) ∅])
                   ([V (in-set Vs)] #:break (> (set-count acc) 1))
           (set-add acc (go V)))))

      (define go : (V → ?Dec)
        (match-lambda
          [(St (and α (α:dyn (β:st-elems _ (== -𝒾-cons)) _)) _) (go-α α)]
          [(Guarded _ (? St/C? (app St/C-tag (== -𝒾-cons))) α) (go-α α)]
          [(-b b) (bool->Dec (null? b))]
          [(-● Ps) (cond [(∋ Ps 'list?) '✓]
                         [(set-ormap list-excl? Ps) '✗]
                         [else #f])]
          [(? α? α) (go-α α)]
          [(? T:@? T) (go* (unpack T Σ))]
          [_ '✗]))
      
      (go V₀)))

  (: join-Dec : (U #t ?Dec) ?Dec → ?Dec)
  (define (join-Dec d d*)
    (cond [(eq? d d*) d*]
          [(eq? d #t) d*]
          [else #f]))

  (: summarize-disj : (℘ ?Dec) → ?Dec)
  ;; Summarize result of `((∨ P ...) → Q)` from results `(P → Q) ...`
  (define (summarize-disj ds)
    (case (set-count ds)
      [(1) (set-first ds)]
      [(2 3) #f]
      [else (error 'summarize-Decs "~a" ds)]))

  (: summarize-conj : (℘ ?Dec) → ?Dec)
  ;; Summarize result of `(P → (∧ Q ...))` from results `(P → Q) ...`
  (define (summarize-conj ds)
    (cond [(= 1 (set-count ds)) (set-first ds)]
          [(∋ ds '✗) '✗]
          [else #f]))

  (define bool-excludes? (set->predicate (get-exclusions 'boolean?)))

  (splicing-local
      ((define (ensure-?Dec [d : (U #t ?Dec)]) : ?Dec
         (case d
           [(#t) !!!]
           [else d]))
       (define (in-D [D : D]) (if (set? D) (in-set D) (in-value D))))
    (: sat^₁ : (D¹ → ?Dec) D → ?Dec)
    (define (sat^₁ check D)
      (ensure-?Dec
       (for/fold ([d : (U #t ?Dec) #t]) ([Vᵢ (in-D D)] #:when d)
         (join-Dec d (check Vᵢ)))))
    (: sat^₂ : (D¹ D¹ → ?Dec) D D → ?Dec)
    (define (sat^₂ check D₁ D₂)
      (ensure-?Dec
       (for*/fold ([d : (U #t ?Dec) #t]) ([Vᵢ (in-D D₁)] [Vⱼ (in-D D₂)] #:when d)
         (join-Dec d (check Vᵢ Vⱼ))))))

  (splicing-local
      ((: distribute₁-V^ : Σ V V^ → (Values (Option V^) (Option V^)))
       (define (distribute₁-V^ Σ P Vs)
         (define-values (Vs:t Vs:f)
           (for/fold ([Vs:t : V^ ∅] [Vs:f : V^ ∅]) ([V (in-set Vs)])
             (case (sat₁ Σ P V)
               [(✓) (values (∪ Vs:t (refine-V V P Σ)) Vs:f)]
               [(✗) (values Vs:t (∪ Vs:f (refine-not-V V P Σ)))]
               [else (values (∪ Vs:t (refine-V V P Σ)) (∪ Vs:f (refine-not-V V P Σ)))])))
         (values (and (not (set-empty? Vs:t)) Vs:t)
                 (and (not (set-empty? Vs:f)) Vs:f)))

       (: distribute₁-T : Σ V S → (Values (Option ΔΣ) (Option ΔΣ)))
       (define (distribute₁-T Σ P T)
         (define (t) (refine-T T P Σ))
         (define (f) (refine-not-T T P Σ))
         (case (sat₁ Σ P T)
           [(✓) (values (t) #f)]
           [(✗) (values #f (f))]
           [else (values (t) (f))])))
    (: distribute₁ : Σ V D → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
    ;; Distribute values into whether or not it satisfies predicate, or both
    (define (distribute₁ Σ P D)
      (if (set? D)
          (let-values ([(?V^₁ ?V^₂) (distribute₁-V^ Σ P D)]
                       [(inj) (λ ([?V^ : (Option V^)]) (and ?V^ (cons (list ?V^) ⊥ΔΣ)))])
            (values (inj ?V^₁) (inj ?V^₂)))
          (let-values ([(?ΔΣ₁ ?ΔΣ₂) (distribute₁-T Σ P D)]
                       [(inj) (λ ([?ΔΣ : (Option ΔΣ)]) (and ?ΔΣ (cons (list D) ?ΔΣ)))])
            (values (inj ?ΔΣ₁) (inj ?ΔΣ₂))))))

  (splicing-local
      ((: distribute₂-V^-V^ : Σ V V^ V^ → (Values (Option W) (Option W)))
       (define (distribute₂-V^-V^ Σ P Vs₁ Vs₂)
         (define-values (Vs₁:t Vs₂:t Vs₁:f Vs₂:f)
           (for*/fold ([Vs₁:t : V^ ∅] [Vs₂:t : V^ ∅] [Vs₁:f : V^ ∅] [Vs₂:f : V^ ∅])
                      ([V₁ (in-set Vs₁)] [V₂ (in-set Vs₂)])
             (case (sat₂ Σ P V₁ V₂)
               [(✓) (values (set-add Vs₁:t V₁) (set-add Vs₂:t V₂) Vs₁:f Vs₂:f)]
               [(✗) (values Vs₁:t Vs₂:t (set-add Vs₁:f V₁) (set-add Vs₂:f V₂))]
               [else (define-values (V₁:t V₂:t) (refine-V-V V₁ V₂ P Σ))
                     (define-values (V₁:f V₂:f) (refine-not-V-V V₁ V₂ P Σ))
                     (values (∪ Vs₁:t V₁:t) (∪ Vs₂:t V₂:t)
                             (∪ Vs₁:f V₁:f) (∪ Vs₂:f V₂:f))])))
         (values (and (not (or (set-empty? Vs₁:t) (set-empty? Vs₂:t))) (list Vs₁:t Vs₂:t))
                 (and (not (or (set-empty? Vs₁:f) (set-empty? Vs₂:f))) (list Vs₁:f Vs₂:f))))

       (: distribute₂-V^-T : Σ V V^ S → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
       (define (distribute₂-V^-T Σ P Vs T)
         (define-values (Vs:t Vs:f ΔΣ:t ΔΣ:f)
           (for/fold ([Vs₁:t : V^ ∅]
                      [Vs₁:f : V^ ∅]
                      [ΔΣ:t : (Option ΔΣ) #f]
                      [ΔΣ:f : (Option ΔΣ) #f])
                     ([V₁ (in-set Vs)])
             (case (sat₂ Σ P V₁ T)
               [(✓) (values (set-add Vs₁:t V₁) Vs₁:f (?ΔΣ⊔ Σ ΔΣ:t ⊥ΔΣ) ΔΣ:f)]
               [(✗) (values Vs₁:t (set-add Vs₁:f V₁) ΔΣ:t (?ΔΣ⊔ Σ ΔΣ:f ⊥ΔΣ))]
               [else (define-values (V₁:t ΔΣ:t*) (refine-V-T V₁ T P Σ))
                     (define-values (V₁:f ΔΣ:f*) (refine-not-V-T V₁ T P Σ))
                     (values (∪ Vs₁:t V₁:t) (∪ Vs₁:f V₁:f) (?ΔΣ⊔ Σ ΔΣ:t ΔΣ:t*) (?ΔΣ⊔ Σ ΔΣ:f ΔΣ:f*))])))
         (values (and (not (set-empty? Vs:t)) ΔΣ:t (cons (list Vs:t T) ΔΣ:t))
                 (and (not (set-empty? Vs:f)) ΔΣ:f (cons (list Vs:f T) ΔΣ:f))))

       (: distribute₂-T-V^ : Σ V S V^ → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
       (define (distribute₂-T-V^ Σ P T Vs)
         (define-values (ΔΣ:t ΔΣ:f Vs:t Vs:f)
           (for/fold ([ΔΣ:t : (Option ΔΣ) #f]
                      [ΔΣ:f : (Option ΔΣ) #f]
                      [Vs₂:t : V^ ∅]
                      [Vs₂:f : V^ ∅])
                     ([V₂ (in-set Vs)])
             (case (sat₂ Σ P T V₂)
               [(✓) (values (?ΔΣ⊔ Σ ΔΣ:t ⊥ΔΣ) ΔΣ:f (set-add Vs₂:t V₂) Vs₂:f)]
               [(✗) (values ΔΣ:t (?ΔΣ⊔ Σ ΔΣ:f ⊥ΔΣ) Vs₂:f (set-add Vs₂:f V₂))]
               [else (define-values (ΔΣ:t* V₂:t) (refine-T-V T V₂ P Σ))
                     (define-values (ΔΣ:f* V₂:f) (refine-not-T-V T V₂ P Σ))
                     (values (?ΔΣ⊔ Σ ΔΣ:t ΔΣ:t*) (?ΔΣ⊔ Σ ΔΣ:f ΔΣ:f*)
                             (∪ Vs₂:t V₂:t) (∪ Vs₂:f V₂:f))])))
         (values (and ΔΣ:t (not (set-empty? Vs:t)) (cons (list T Vs:t) ΔΣ:t))
                 (and ΔΣ:f (not (set-empty? Vs:f)) (cons (list T Vs:f) ΔΣ:f))))

       (: distribute₂-T-T : Σ V S S → (Values (Option ΔΣ) (Option ΔΣ)))
       (define (distribute₂-T-T Σ P T₁ T₂)
         (define (t) (refine-T-T T₁ T₂ P Σ))
         (define (f) (refine-not-T-T T₁ T₂ P Σ))
         (case (sat₂ Σ P T₁ T₂)
           [(✓) (values (t) #f)]
           [(✗) (values #f (f))]
           [else (values (t) (f))])))
    (: distribute₂ : Σ V D D → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
    ;; Distribute value whether or not they satisfy predicate, or both
    (define (distribute₂ Σ P D₁ D₂)
      (cond
        [(and (set? D₁) (set? D₂))
         (define-values (?W₁ ?W₂) (distribute₂-V^-V^ Σ P D₁ D₂))
         (define (inj [?W : (Option W)]) (and ?W (cons ?W ⊥ΔΣ)))
         (values (inj ?W₁) (inj ?W₂))]
        [(set? D₁) (distribute₂-V^-T Σ P D₁ D₂)]
        [(set? D₂) (distribute₂-T-V^ Σ P D₁ D₂)]
        [else
         (define-values (ΔΣ:t ΔΣ:f) (distribute₂-T-T Σ P D₁ D₂))
         (define (inj [?ΔΣ : (Option ΔΣ)]) (and ?ΔΣ (cons (list D₁ D₂) ?ΔΣ)))
         (values (inj ΔΣ:t) (inj ΔΣ:f))])))

  (: refine-V^ : V^ (U V V^) Σ → V^)
  ;; Refine abstract value `Vs` with predicate(s) `P*`
  (define (refine-V^ Vs P* Σ)
    (define (go [P : V] [Vs : V^])
      (for/fold ([acc : V^ ∅]) ([V (in-set Vs)])
        (case (sat₁ Σ P V)
          [(✓) (set-add acc V)]
          [(✗) acc]
          [else (∪ acc (refine-V V P Σ))])))
    (if (set? P*) (set-fold go Vs P*) (go P* Vs)))

  (: refine-not-V^ : V^ V Σ → V^)
  (define (refine-not-V^ Vs P Σ)
    (for*/fold ([acc : V^ ∅]) ([V (in-set Vs)])
      (case (sat₁ Σ P V)
        [(✓) acc]
        [(✗) (set-add acc V)]
        [else (∪ acc (refine-not-V V P Σ))])))

  (:* refine-V refine-not-V : V V Σ → V^)
  ;; Refine value `V` with predicate `P`
  (define (refine-V V P Σ)
    (match V
      [(-● Ps)
       ;; TODO reduce hack. This comes from `one-of/c` not recognized as a refinement
       (match P
         [(One-Of/C bs) (refine-V^ (map/set -b bs) Ps Σ)]
         [_ (reify (refine-Ps Ps P))])]
      [(St α Ps) {set (St α (refine-Ps Ps P))}]
      [_ {set V}]))
  (define (refine-not-V V P Σ)
    (cond [(and (P? P) (?negate P)) => (λ (¬P) (refine-V V ¬P Σ))]
          [else {set V}]))

  (:* refine-T refine-not-T : S V Σ → ΔΣ)
  (define (refine-T T₀ P₀ Σ)
    (match-define (cons Ξ Γ) Σ)
    (if (and (P? P₀) (T? T₀))
        (let go ([T : T T₀] [P : P P₀])
          (match T
            [(T:@ (? -st-ac? ac) (list T*)) (go (assert T* T?) (P:St ac P))]
            [_ (cons ⊥Ξ (hash T (refine-V^ (unpack T Σ) P Σ)))]))
        ⊥ΔΣ))
  (define (refine-not-T T P Σ)
    (cond [(and (P? P) (?negate P)) => (λ (¬P) (refine-T T ¬P Σ))]
          [else ⊥ΔΣ]))

  (: ?ΔΣ⊔ : Σ (Option ΔΣ) ΔΣ → ΔΣ)
  (define (?ΔΣ⊔ Σ ?ΔΣ ΔΣ)
    (if ?ΔΣ (ΔΣ⊔ Σ ?ΔΣ ΔΣ) ΔΣ))


  ;;;;; Congruence closure stuff
  ;;FIXME: refactor
  (splicing-local
      (;; Return list of term successors
       (define succ : (S → (Listof S))
         (match-lambda
           [(T:@ _ Ts) Ts]
           [_ '()]))

       ;; Return node label for term
       (define lab : (S → Any)
         (match-lambda
           [(T:@ K _) K]
           [S S]))

       ;; Generate additional axioms for appropriate terms
       (define gen-eqs : (S → (℘ (Pairof S S)))
         (match-lambda
           ;; e.g. (car (cons x y)) ≡ x
           ;; FIXME do properly for substructs
           [(and T (T:@ (-st-mk 𝒾) Ts))
            (for/set: : (℘ (Pairof S S)) ([Tᵢ (in-list Ts)]
                                          [i (in-range (count-struct-fields 𝒾))])
              (cons (T:@ (-st-ac 𝒾 (assert i index?)) (list T)) Tᵢ))]
           [(T:@ (-st-ac 𝒾 _) (and arg (list T*)))
            (define fields (build-list (count-struct-fields 𝒾)
                                       (λ ([i : Index]) (T:@ (-st-ac 𝒾 i) arg))))
            {set (cons T* (T:@ (-st-mk 𝒾) fields))}]
           ;; e.g. 0 + x = x
           [(T:@ '+ (list T₁ T₂))
            {set (cons (T:@ '+ (list T₁ -zero)) T₁)
                 (cons (T:@ '+ (list -zero T₁)) T₁)
                 (cons (T:@ '+ (list T₂ -zero)) T₂)
                 (cons (T:@ '+ (list -zero T₂)) T₂)}]
           [_ ∅]))

       (: make-congruence-closer : (S → (℘ S)) → (Values (S S → Void) (S S → Boolean)))
       ;; https://dl.acm.org/citation.cfm?id=322198 , section 2
       (define (make-congruence-closer preds)
         (define-values (union! find) ((inst make-union-find S)))
         (define equivs : (Mutable-HashTable S (℘ S)) (make-hash))
         (define (equivs-of [x : S]) #;(assert (equal? x (find x))) (hash-ref equivs x (λ () {set x})))
         (define (preds-of [xs : (℘ S)])
           (for/union : (℘ S) ([x (in-set xs)])
             (preds x)))

         (: merge! : S S → Void)
         ;; Mark `u` and `v` as being in the same partition and extend congruence closure
         (define (merge! u v)
           (define u* (find u))
           (define v* (find v))
           (unless (equal? u* v*)
             (define u*:equivs (equivs-of u*))
             (define v*:equivs (equivs-of v*))
             (define Pᵤ (preds-of u*:equivs))
             (define Pᵥ (preds-of v*:equivs))
             (union! u v)
             (begin ; clean up `equivs` just for easy debugging later
               (hash-remove! equivs u*)
               (hash-remove! equivs v*)
               (hash-set! equivs (find u) (∪ u*:equivs v*:equivs)))
             (for* ([x (in-set Pᵤ)]
                    [y (in-set Pᵥ)]
                    #:when (congruent? x y))
               (merge! x y))))

         (: congruent? : S S → Boolean)
         (define (congruent? x y)
           (and (equal? (lab x) (lab y))
                (let ([us (succ x)]
                      [vs (succ y)])
                  (and (equal? (length us) (length vs))
                       (for/and : Boolean ([u (in-list us)] [v (in-list vs)])
                         (equal? (find u) (find v)))))))

         (values merge! (λ (x y) (equal? (find x) (find y)))))

       (: fold-terms (∀ (A)
                        (S A → A)
                        A
                        (Listof (Pairof S S))
                        (Listof (Pairof S S)) → A))
       (define (fold-terms step acc eqs diseqs)
         (: on-x : S A → A)
         (define (on-x x a) (foldl on-x (step x a) (succ x)))
         (: on-xx : (Pairof S S) A → A)
         (define (on-xx xx xs) (on-x (cdr xx) (on-x (car xx) xs)))
         (foldl on-xx (foldl on-xx acc eqs) diseqs))

       (: sat? : (Listof (Pairof S S)) (Listof (Pairof S S)) → Boolean)
       ;; Check if given equalities and dis-equalities are satisfiable
       ;; https://dl.acm.org/citation.cfm?id=322198, section 3
       (define (sat? eqs diseqs)
         (define-values (merge! ≡)
           (let ([m
                  ((inst fold-terms (HashTable S (℘ S)))
                   (λ (x m)
                     (foldl (λ ([x* : S] [m : (HashTable S (℘ S))])
                              (hash-update m x* (λ ([xs : (℘ S)]) (set-add xs x)) mk-∅))
                            m
                            (succ x)))
                   (hash) eqs diseqs)])
             (make-congruence-closer (λ (x) (hash-ref m x mk-∅)))))
         (for ([eq (in-list eqs)])
           (merge! (car eq) (cdr eq)))
         (not (for/or : Boolean ([diseq (in-list diseqs)])
                (≡ (car diseq) (cdr diseq))))))
    (: sat/extra? : (Listof (Pairof S S)) (Listof (Pairof S S)) → Boolean)
    ;; Given extra assumptions generated by `gen-eqs`, check if given equalities
    ;; and dis-equalities are satisfiable
    ;; https://dl.acm.org/citation.cfm?id=322198, section 4
    (define (sat/extra? eqs diseqs)
      (define all-eqs
        (let ([more-eqs
               ((inst fold-terms (℘ (Pairof S S)))
                (λ (x acc) (set-union acc (gen-eqs x)))
                ∅ eqs diseqs)])
          (append (set->list more-eqs) eqs)))
      (sat? all-eqs diseqs)))

    (: base? : Base → Boolean : Base)
    (define (base? _) #t)
  )
