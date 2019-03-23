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
         "../execution/signatures.rkt" ; TODO just for debugging
         ) 

(define-unit prover@
  (import static-info^ meta-functions^
          sto^ val^ pretty-print^
          prims^
          exec^)
  (export prover^)

  (: sat : Σ V V^ → ?Dec)
  (define (sat Σ P V) (sat^₁ (λ (V) (sat₁ Σ P V)) V))

  (: maybe=? : Σ Integer V^ → Boolean)
  ;; Check if value `V` can possibly be integer `i`
  (define (maybe=? Σ i Vs)
    (set-ormap (λ ([V : V]) (and (memq (sat₂ Σ 'equal? (-b i) V) '(✓ #f)) #t)) Vs))

  (: check-plaus : Σ V W → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))
  (define (check-plaus Σ P W)
    (match W
      [(list V    ) (collect sat₁ refine₁ refine-not₁ Σ P V)]
      [(list V₁ V₂) (collect sat₂ refine₂ refine-not₂ Σ P V₁ V₂)]
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
      [(P:≡ (? -b? b)) {set b}]
      [_ #f]))

  (: refine : V^ (U V (℘ P)) Σ → (Values V^ ΔΣ))
  (define (refine Vs P* Σ)
    (if (set? P*)
        ;; refine by conjunction of predicates
        (for*/fold ([Vs : V^ Vs] [ΔΣ : ΔΣ ⊥ΔΣ]) ([P (in-set P*)])
          (define-values (Vs* ΔΣ*) (refine Vs P Σ))
          (values Vs* (⧺ ΔΣ ΔΣ*)))
        (let-values ([(acc ΔΣ*)
                      (for*/fold ([acc : V^ ∅] [ΔΣ : (Option ΔΣ) #f])
                                 ([V (in-set Vs)]
                                  [P (if (α? P*) (in-set (unpack P* Σ)) (in-value P*))])
                        (case (sat₁ Σ P V)
                          [(✓) (values (set-add acc V) (?ΔΣ⊔ ΔΣ ⊥ΔΣ))]
                          [(✗) (values acc (?ΔΣ⊔ ΔΣ ⊥ΔΣ))]
                          [else (define-values (V* ΔΣ*) (refine₁ V P Σ))
                                (values (∪ acc V*) (?ΔΣ⊔ ΔΣ ΔΣ*))]))])
          (values acc (assert ΔΣ*)))))

  (: refine-not : V^ V Σ → (Values V^ ΔΣ))
  (define (refine-not Vs P Σ)
    (define-values (acc ΔΣ*)
      (for*/fold ([acc : V^ ∅] [ΔΣ : (Option ΔΣ) #f])
                 ([V (in-set Vs)]
                  [P (if (α? P) (in-set (unpack P Σ)) (in-value P))])
        (case (sat₁ Σ P V)
          [(✓) (values acc (?ΔΣ⊔ ΔΣ ⊥ΔΣ))]
          [(✗) (values (set-add acc V) (?ΔΣ⊔ ΔΣ ⊥ΔΣ))]
          [else (define-values (V* ΔΣ*) (refine-not₁ V P Σ))
                (values (∪ acc V*) (?ΔΣ⊔ ΔΣ ΔΣ*))])))
    (values acc (assert ΔΣ*)))

  (: refine₁ : V V Σ → (Values V^ ΔΣ))
  (define (refine₁ V P Σ)
    (match V
      [(or (? -●?) (? St?)) (values (refine-V V P Σ) ⊥ΔΣ)]
      [(? T? T) (values {set T} (if (ambiguous? T Σ) ⊥ΔΣ (refine-T T P Σ)))]
      [_ (values {set V} ⊥ΔΣ)]))

  (: refine-T : T V Σ → ΔΣ)
  (define (refine-T T₀ P Σ)
    (if (P? P)
        (let go ([T : (U T -b) T₀] [acs : (Listof -st-ac) '()])
          (match T
            [(T:@ (? -st-ac? ac) (list T*)) (go T* (cons ac acs))]
            [(? α? α) (mut α (refine-V^ (unpack α Σ) (if (pair? acs) (P:St acs P) P) Σ) Σ)]
            [_ ⊥ΔΣ]))
        ⊥ΔΣ))

  (: refine-not₁ : V V Σ → (Values V^ ΔΣ))
  (define (refine-not₁ V P Σ)
    (match P
      [(? Q?) (refine₁ V (P:¬ P) Σ)]
      [(P:¬ Q) (refine₁ V Q Σ)]
      [(P:St acs (? Q? Q)) (refine₁ V (P:St acs (P:¬ Q)) Σ)]
      [(P:St acs (P:¬ Q)) (refine₁ V (P:St acs Q) Σ)]
      [_ (values {set V} ⊥ΔΣ)]))

  (: refine₂ : V V V Σ → (Values V^ V^ ΔΣ))
  (define (refine₂ V₁ V₂ P Σ)
    (match P
      ['<  (refine-both V₁ P:< V₂ P:> Σ)]
      ['<= (refine-both V₁ P:≤ V₂ P:≥ Σ)]
      ['>  (refine-both V₁ P:> V₂ P:< Σ)]
      ['>= (refine-both V₁ P:≥ V₂ P:≤ Σ)]
      ['=  (refine-both V₁ P:= V₂ P:= Σ)]
      [(or 'equal? 'eq? 'eqv? 'char=? 'string=?)
       (refine-both V₁ P:≡ V₂ P:≡ Σ)]
      [_ (values {set V₁} {set V₂} ⊥ΔΣ)]))

  (: refine-not₂ : V V V Σ → (Values V^ V^ ΔΣ))
  (define (refine-not₂ V₁ V₂ P Σ)
    (define (default) (values {set V₁} {set V₂} ⊥ΔΣ))
    (define (refine [P* : Q]) (refine₂ V₁ V₂ P* Σ))
    (match P
      ['< (refine '>=)]
      ['<= (refine '>)]
      ['> (refine '<=)]
      ['>= (refine '<)]
      [(or 'equal? 'eq? 'eqv? 'char=? 'string=?)
       (define P* (compose1 P:¬ P:≡))
       (refine-both V₁ P* V₂ P* Σ)]
      [_ (default)]))

  (: refine-V^ : V^ (U V V^) Σ → V^)
  (define (refine-V^ Vs P* Σ)
    (define (go [P : V] [Vs : V^])
      (for/fold ([acc : V^ ∅]) ([V (in-set Vs)])
        (case (sat₁ Σ P V)
          [(✓) (set-add acc V)]
          [(✗) acc]
          [else (∪ acc (refine-V V P Σ))])))
    (if (set? P*) (set-fold go Vs P*) (go P* Vs)))

  (: refine-V : V V Σ → V^)
  (define (refine-V V P Σ)
    (match V
      [(-● Ps)
       ;; TODO reduce hack. This comes from `one-of/c` not recognized as a refinement
       (match P
         [(One-Of/C bs) (refine-V^ (map/set -b bs) Ps Σ)]
         [_ (reify (refine-Ps Ps P Σ))])]
      [(St α Ps) {set (St α (refine-Ps Ps P Σ))}]
      [_ {set V}]))

  (: refine-Ps : (℘ P) V Σ → (℘ P))
  ;; Strengthen refinement set with new predicate
  (define (refine-Ps Ps₀ P₀ Σ)
    ;; Combine 2 predicates for a more precise one.
    ;; Return `#f` if there's no single predicate that refines both
    (define P+ : (P P → (Option (Listof P)))
      (match-lambda**/symmetry
       [(P Q) #:when (equal? '✓ (P⊢P Σ P Q)) (list P)]
       [((or 'exact-integer? 'exact-nonnegative-integer?)
         (P:≥ (-b (and (? (between/c 0 1)) (not 0)))))
        (list 'exact-positive-integer?)]
       [((or 'exact-integer? 'exact-nonnegative-integer?)
         (P:> (-b (and (? (between/c 0 1)) (not 1)))))
        (list 'exact-positive-integer?)]
       [('exact-integer? (P:≥ (-b (and (? (between/c -1 0)) (not -1)))))
        (list 'exact-nonnegative-integer?)]
       [('exact-integer? (P:> (-b (and (? (between/c -1 0)) (not  0)))))
        (list 'exact-nonnegative-integer?)]
       [((or 'exact-integer? 'exact-nonnegative-integer?) 'zero?)
        (list (P:≡ -zero))]
       [('exact-nonnegative-integer? (P:¬ (P:= (-b 0))))
        (list 'exact-positive-integer?)]
       [('list? (P:¬ 'null?)) (list 'list? -cons?)]
       [('list? (P:¬ -cons?)) (list 'null?)]
       [((and P (or (? P:>?) (? P:≥?) (? P:<?) (? P:≤?))) 'number?)
        (list P 'real?)]
       #:else
       [(P₀ Q₀)
        (match* (P₀ Q₀)
          [((P:St acs P*) (P:St acs Q*))
           (match (P+ P* Q*)
             [(? values Ps) (map (λ ([P : P]) (P:St acs P)) Ps)]
             [_ #f])]
          [(_ _) #f])]))
    (if (P? P₀) (merge/compact P+ P₀ Ps₀) Ps₀))

  (: sat₁ : Σ V V → ?Dec)
  (define (sat₁ Σ P V₀)
    (match V₀
      [(-● Ps) (Ps⊢P Σ Ps P)]
      [(? α? α) (sat^₁ (λ (V) (sat₁ Σ P V)) (unpack α Σ))]
      [(and T (T:@ k _)) (or (and (symbol? k) (P⊢P Σ (get-conservative-range k) P))
                             (sat^₁ (λ (V) (sat₁ Σ P V)) (unpack T Σ)))]
      [_ (match P
           [(-st-p 𝒾)
            (match V₀
              [(or (St (α:dyn (β:st-elems _ 𝒾*) _) _)
                   (Guarded _ (? St/C? (app St/C-tag 𝒾*)) _))
               (bool->Dec (and 𝒾* (𝒾* . substruct? . 𝒾)))]
              [_ '✗])]
           [(One-Of/C bs) (bool->Dec (and (-b? V₀) (∋ bs (-b-unboxed V₀))))]
           [(P:¬ Q) (neg (sat₁ Σ Q V₀))]
           [(P:≥ T) (sat₂ Σ '>= V₀ T)]
           [(P:> T) (sat₂ Σ '>  V₀ T)]
           [(P:≤ T) (sat₂ Σ '<= V₀ T)]
           [(P:< T) (sat₂ Σ '<  V₀ T)]
           [(P:= T) (sat₂ Σ '=  V₀ T)]
           [(P:≡ T) (sat₂ Σ 'equal? V₀ T)]
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
                [(Clo xs _ _ _) (arity-includes? (shape xs) 1)]
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
               (check-among Fn/C? And/C? Or/C? Not/C? X/C?
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
               (define go : (V → ?Dec)
                 (match-lambda
                   [(-b b) (bool->Dec (immutable? b))]
                   [(or (? Empty-Hash?) (? Hash-Of?) (? Empty-Set?) (? Set-Of?)) '✓]
                   [(Guarded _ (or (? Hash/C?) (? Set/C?)) α) (go-α α)]
                   [(or (? Vect?) (? Vect-Of?) (Guarded _ (or (? Vect/C?) (? Vectof/C?)) _)) '✗]
                   [(-● Ps) (Ps⊢P Σ Ps 'immutable?)]
                   [_ #f]))
               (: go-α : α → ?Dec)
               (define (go-α α) (sat^₁ go (unpack α Σ)))
               (go V₀)]
              [(list?) (check-proper-list Σ V₀)]
              [(port? input-port? output-port?) '✗] ; ports can't reach here
              [else (and (bool-excludes? (get-conservative-range P)) '✓)])]
           [_ #f])]))

  (: sat₂ : Σ V V V → ?Dec)
  (define (sat₂ Σ P V₁ V₂)
    (define (go [V₁ : V] [V₂ : V]) : ?Dec
      (case P
        [(equal? eq? char=? string=?) (check-equal? Σ V₁ V₂)]
        [(=) (match* (V₁ V₂)
               [((-b (? real? x)) (-b (? real? y))) (bool->Dec (= x y))]
               [(_ _) #f])]
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
          [(and (T? V₁) (-b? V₂)) (sat^₂ go (unpack V₁ Σ) {set V₂})]
          [(and (-b? V₁) (T? V₂)) (sat^₂ go {set V₁} (unpack V₂ Σ))]
          [(and (T? V₁) (T? V₂)) (or (sat^₂ go (unpack V₁ Σ) {set V₂})
                                     (sat^₂ go {set V₁} (unpack V₂ Σ))
                                     (sat^₂ go (unpack V₁ Σ) (unpack V₂ Σ)))]
          [else #f]))

  (: check-≤ : Σ V V → ?Dec)
  (define (check-≤ Σ V₁ V₂)
    (match* (V₁ V₂)
      [((-b (? real? x)) (-b (? real? y))) (bool->Dec (<= x y))]
      [((-b (? real? x)) (-● Ps))
       (for/or : ?Dec ([P (in-set Ps)])
         (match P
           [(or (P:≥ (-b (? real? y))) (P:> (-b (? real? y)))) #:when (and y (>= y x)) '✓]
           [(P:< (-b (? real? y))) #:when (<= y x) '✗]
           ['exact-nonnegative-integer? #:when (<= x 0) '✓]
           ['exact-positive-integer? #:when (<= x 1) '✓]
           [_ #f]))]
      [((-● Ps) (-b (? real? y)))
       (for/or : ?Dec ([P (in-set Ps)])
         (match P
           [(P:< (-b (? real? x))) (and (<= x y) '✓)]
           [(P:≤ (-b (? real? x))) (and (<= x y) '✓)]
           [(P:> (-b (? real? x))) (and (>= x y) '✗)]
           [(P:≥ (-b (? real? x))) (and (>  x y) '✗)]
           [(P:= (-b (? real? x))) (bool->Dec (<= x y))]
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
      [(_ _) #f]))

  (: check-equal? : Σ V V → ?Dec)
  (define (check-equal? Σ V₁ V₂)

    (: go : T T → ?Dec)
    (define (go T₁ T₂)
      (if (and (equal? T₁ T₂) (not (ambiguous? T₁ Σ)))
          '✓
          ; TODO watch out for loops
          (go-V^ (unpack T₁ Σ) (unpack T₂ Σ)))) 
    
    (: go-V^ : V^ V^ → ?Dec)
    (define (go-V^ Vs₁ Vs₂) (sat^₂ go-V Vs₁ Vs₂))

    (: go-V : V V → ?Dec)
    (define go-V
      (match-lambda**
       [((? -prim? x) (? -prim? y)) (bool->Dec (equal? x y))]
       [((-● Ps) (and T (or (? -b?) (? T?)))) (Ps⊢P Σ Ps (P:≡ T))]
       [((and T (or (? -b?) (? T?))) (-● Ps)) (Ps⊢P Σ Ps (P:≡ T))]
       [((? -prim?) (not (or (? -●?) (? T?) (? -prim?)))) '✗]
       [((not (or (? -●?) (? T?) (? -prim?))) (? -prim?)) '✗]
       [((St (and α₁ (α:dyn (β:st-elems _ 𝒾₁) _)) _)
         (St (and α₂ (α:dyn (β:st-elems _ 𝒾₂) _)) _))
        (cond [(not (equal? 𝒾₁ 𝒾₂)) #f]
              [(and (equal? α₁ α₂) (not (ambiguous? α₁ Σ))) '✓]
              [else
               (for/fold ([acc : ?Dec '✓])
                         ([Vs₁ (in-vector (Σ@/blob α₁ Σ))]
                          [Vs₂ (in-vector (Σ@/blob α₂ Σ))]
                          #:break (eq? acc '✗))
                 (case (go-V^ Vs₁ Vs₂)
                   [(✓) acc]
                   [(✗) '✗]
                   [(#f) #f]))])]
       [((? T? T₁) (? T? T₂)) (go T₁ T₂)]
       [((? T? T) V) (go-V^ (unpack T Σ) (unpack V Σ))]
       [(V (? T? T)) (go-V^ (unpack V Σ) (unpack T Σ))]
       [(_ _) #f]))

    (go-V V₁ V₂))

  (:* Ps⊢P simple-Ps⊢P : Σ (℘ P) V → ?Dec)
  (define (Ps⊢P Σ Ps Q)
    (define Q* (canonicalize Q))
    (if (set? Q*)
        (summarize-conj (map/set (λ ([Q : P]) (simple-Ps⊢P Σ Ps Q)) Q*))
        (simple-Ps⊢P Σ Ps Q*)))
  (define (simple-Ps⊢P Σ Ps Q)
    (cond [(∋ Ps Q) '✓]
          [(and (equal? Q -cons?) (∋ Ps (P:¬ 'null?)) (∋ Ps 'list?)) '✓]
          [(equal? Q 'none/c) '✗]
          [(equal? Q 'any/c) '✓]
          [else (for/or : ?Dec ([P (in-set Ps)]) (P⊢P Σ P Q))]))

  (:* P⊢P simple-P⊢P : Σ V V → ?Dec)
  ;; Need `Σ` because of predicates such as `(P≥ x)`
  (define (P⊢P Σ P₀ Q₀)
    (define P* (canonicalize P₀))
    (define Q* (canonicalize Q₀))
    (cond [(and (set? P*) (set? Q*))
           (summarize-conj (map/set (λ ([Q : P]) (simple-Ps⊢P Σ P* Q)) Q*))]
          [(set? Q*)
           (summarize-conj (map/set (λ ([Q : P]) (simple-P⊢P Σ P* Q)) Q*))]
          [(set? P*) (simple-Ps⊢P Σ P* Q*)]
          [else (simple-P⊢P Σ P* Q*)]))
  (define (simple-P⊢P Σ P Q)
    (match* (P Q)
      ;; Base
      [(_ 'any/c) '✓]
      [('none/c _) '✓]
      [(_ 'none/c) '✗]
      [('any/c _) #f]
      [(P P) '✓]
      [((P:St acs P*) (P:St acs Q*)) (simple-P⊢P Σ P* Q*)]
      [((? symbol? P) (? symbol? Q)) (o⊢o P Q)]
      [((? -o? P) 'values) (match P ; TODO generalize
                             ['not '✗]
                             [_ #|TODO careful|# '✓])]
      [((-st-p 𝒾₁) (-st-p 𝒾₂)) (bool->Dec (𝒾₁ . substruct? . 𝒾₂))]
      [((? base-only?) (? -st-p?)) '✗]
      [((? -st-p?) (? base-only?)) '✗]
      [((One-Of/C bs) (P:≡ (-b b)))
       (if (∋ bs b)
           (if (> (set-count bs) 1) #f '✓)
           '✗)]
      [((P:≡ (-b b)) (One-Of/C bs)) (bool->Dec (∋ bs b))]
      [((P:≡ (? -b?)) (or (? -st-p?) 'vector? 'set? 'hash?)) '✗]
      [((or (? -st-p?) 'vector? 'set? 'hash?) (P:≡ (? -b?))) '✗]
      ;; Negate
      [((P:¬ P) (P:¬ Q)) (case (simple-P⊢P Σ Q P)
                           [(✓) '✓]
                           [else #f])]
      [(P (P:¬ Q)) (neg (simple-P⊢P Σ P Q))]
      [((P:¬ P) Q) (case (simple-P⊢P Σ Q P)
                     [(✓) '✗]
                     [else #f])]
      ;; Special rules for numbers
      ; < and <
      [((P:≤ (-b (? real? a))) (P:< (-b (? real? b))))
       (and (<  a b) '✓)]
      [((or (P:< (-b (? real? a))) (P:≤ (-b (? real? a))))
        (or (P:< (-b (? real? b))) (P:≤ (-b (? real? b)))))
       (and a b (<= a b) '✓)]
      ; > and >
      [((P:≥ (-b (? real? a))) (P:> (-b (? real? b))))
       (and (>  a b) '✓)]
      [((or (P:> (-b (? real? a))) (P:≥ (-b (? real? a))))
        (or (P:> (-b (? real? b))) (P:≥ (-b (? real? b)))))
       (and a b (>= a b) '✓)]
      ; < and >
      [((P:≤ (-b (? real? a))) (P:≥ (-b (? real? b))))
       (and (<  a b) '✗)]
      [((or (P:< (-b (? real? a))) (P:≤ (-b (? real? a))))
        (or (P:> (-b (? real? b))) (P:≥ (-b (? real? b)))))
       (and a b (<= a b) '✗)]
      ; > and <
      [((P:≥ (-b (? real? a))) (P:≤ (-b (? real? b))))
       (and (>  a b) '✗)]
      [((or (P:> (-b (? real? a))) (P:≥ (-b (? real? a))))
        (or (P:< (-b (? real? b))) (P:≤ (-b (? real? b)))))
       (and a b (>= a b) '✗)]
      ; _ -> real?
      ;; `(P T)` subsuming `real?` causes problem when `(P T)` gets dropped
      ;; due to `T` going out of scope
      #;[((or (? P:<?) (? P:≤?) (? P:>?) (? P:≥?) (? P:=?)) (or 'real? 'number?)) '✓]
      [((P:= (and b (-b (? real?)))) Q) (sat₁ Σ Q b)]
      ; equal?
      [((P:= (-b (? real? x))) (P:= (-b (? real? y)))) (bool->Dec (= x y))]
      [((P:< (-b (? real? a))) (P:= (-b (? real? b)))) #:when (<= a b) '✗]
      [((P:≤ (-b (? real? a))) (P:= (-b (? real? b)))) #:when (<  a b) '✗]
      [((P:> (-b (? real? a))) (P:= (-b (? real? b)))) #:when (>= a b) '✗]
      [((P:≥ (-b (? real? a))) (P:= (-b (? real? b)))) #:when (>  a b) '✗]
      [((P:= (-b (? real? a))) (P:< (-b (? real? b)))) (bool->Dec (<  a b))]
      [((P:= (-b (? real? a))) (P:≤ (-b (? real? b)))) (bool->Dec (<= a b))]
      [((P:= (-b (? real? a))) (P:> (-b (? real? b)))) (bool->Dec (>  a b))]
      [((P:= (-b (? real? a))) (P:≥ (-b (? real? b)))) (bool->Dec (>= a b))]
      ;; Regardless of terms
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
      ['exact-nonnegative-integer? {set 'exact? 'integer? (P:≥ -zero)}]
      ['exact-positive-integer? {set 'exact? 'integer? (P:> -zero)}]
      ['exact-integer? {set 'exact? 'integer?}]
      ['positive? (P:> -zero)]
      ['negative? (P:< -zero)]
      ['zero? (P:= -zero)]
      [(P:¬ 'even?) 'odd?]
      [(P:¬ 'odd?) 'even?]
      [(and P₀ (P:St acs P*))
       (define P** (canonicalize P*))
       (cond [(eq? P** P*) P₀] ; try to re-use old instance
             [(set? P**) (map/set (λ ([P : P]) (P:St acs P)) P**)]
             [(P? P**) (P:St acs P**)]
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
          [(? T:@? T) (go* (unpack T Σ))]))
      
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
           [else d])))
    (: sat^₁ : (V → ?Dec) V^ → ?Dec)
    (define (sat^₁ check V)
      (ensure-?Dec
       (for/fold ([d : (U #t ?Dec) #t]) ([Vᵢ (in-set V)] #:when d)
         (join-Dec d (check Vᵢ)))))
    (: sat^₂ : (V V → ?Dec) V^ V^ → ?Dec)
    (define (sat^₂ check V₁ V₂)
      (ensure-?Dec
       (for*/fold ([d : (U #t ?Dec) #t]) ([Vᵢ (in-set V₁)] [Vⱼ (in-set V₂)] #:when d)
         (join-Dec d (check Vᵢ Vⱼ))))))

  (define-syntax-parser collect
    [(_ sat:id refine:id refine-not:id Σ:id P:id Vs:id ...)
     (with-syntax ([(V ...) (generate-temporaries #'(Vs ...))]
                   [(V:t ...) (generate-temporaries #'(Vs ...))]
                   [(V:f ...) (generate-temporaries #'(Vs ...))]
                   [(Vs:t ...) (generate-temporaries #'(Vs ...))]
                   [(Vs:f ...) (generate-temporaries #'(Vs ...))])
       #'(let-values ([(Vs:t ... ΔΣ:t Vs:f ... ΔΣ:f)
                       (for*/fold ([Vs:t : V^ ∅] ... [ΔΣ:t : (Option ΔΣ) #f]
                                   [Vs:f : V^ ∅] ... [ΔΣ:f : (Option ΔΣ) #f])
                                  ([V (in-set Vs)] ...)
                         (case (sat Σ P V ...)
                           [(✓) (values (set-add Vs:t V) ... (?ΔΣ⊔ ΔΣ:t ⊥ΔΣ)
                                        Vs:f ... (?ΔΣ⊔ ΔΣ:f ⊥ΔΣ))]
                           [(✗) (values Vs:t ... (?ΔΣ⊔ ΔΣ:t ⊥ΔΣ)
                                        (set-add Vs:f V) ... (?ΔΣ⊔ ΔΣ:f ⊥ΔΣ))]
                           [else (let-values ([(V:t ... ΔΣ:t*) (refine V ... P Σ)]
                                              [(V:f ... ΔΣ:f*) (refine-not V ... P Σ)])
                                   (values (∪ Vs:t V:t) ... (?ΔΣ⊔ ΔΣ:t ΔΣ:t*)
                                           (∪ Vs:f V:f) ... (?ΔΣ⊔ ΔΣ:f ΔΣ:f*)))]))])
           (values (and (not (or (set-empty? Vs:t) ...))
                        (cons (list Vs:t ...) (assert ΔΣ:t)))
                   (and (not (or (set-empty? Vs:f) ...))
                        (cons (list Vs:f ...) (assert ΔΣ:f))))))])

  (: refine-both : V ((U T -b) → P) V ((U T -b) → P) Σ → (Values V^ V^ ΔΣ))
  (define (refine-both V₁ P₁ V₂ P₂ Σ)
    (define-values (V₁* ΔΣ₁) (if (and (T? V₁) (or (-b? V₂) (T? V₂)))
                                 (refine₁ V₁ (P₁ V₂) Σ)
                                 (values {set V₁} ⊥ΔΣ)))
    (define-values (V₂* ΔΣ₂) (if (and (T? V₂) (or (-b? V₁) (T? V₁)))
                                 (refine₁ V₂ (P₂ V₁) Σ)
                                 (values {set V₂} ⊥ΔΣ)))
    (values V₁* V₂* (⧺ ΔΣ₁ ΔΣ₂)))

  (: ?ΔΣ⊔ : (Option ΔΣ) ΔΣ → ΔΣ)
  (define (?ΔΣ⊔ ?ΔΣ ΔΣ)
    (if ?ΔΣ (ΔΣ⊔ ?ΔΣ ΔΣ) ΔΣ))
  )
