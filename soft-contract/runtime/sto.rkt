#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         racket/vector
         racket/splicing
         (only-in racket/function curry)
         set-extras
         unreachable
         (only-in "../utils/map.rkt" dom)
         "../utils/vector.rkt"
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit sto@
  (import static-info^
          val^ prover^ pretty-print^)
  (export sto^) 

  (: ⧺ : ΔΣ ΔΣ * → ΔΣ)
  ;; Combine store deltas. *Not* commutative due to strong updates when possible.
  ;; (A store is a special case of store-delta where the cardinality is positive)
  (define (⧺ ΔΣ₀ . ΔΣs)
    (: comb (∀ (X Y)
               (X Y (Immutable-HashTable X Y) → (Immutable-HashTable X Y))
               ((Immutable-HashTable X Y) X Y → (Immutable-HashTable X Y))
               (Immutable-HashTable X Y)
               (Immutable-HashTable X Y)
               → (Immutable-HashTable X Y)))
    (define (comb ⧺ˡ ⧺ʳ m acc)
      (if (> (hash-count acc) (hash-count m))
          (for/fold ([acc : (Immutable-HashTable X Y) acc]) ([(x y) (in-hash m)])
            (⧺ʳ acc x y))
          (for/fold ([m : (Immutable-HashTable X Y) m]) ([(x y) (in-hash acc)])
            (⧺ˡ x y m))))
    (define (⧺₁ [ΔΣᵢ : ΔΣ] [acc : ΔΣ])
      (match-define (cons ΔΞᵢ ΔΓᵢ) ΔΣᵢ)
      (match-define (cons ΔΞₐ ΔΓₐ) acc)
      (cons (comb Ξ:⧺ˡ Ξ:⧺ʳ ΔΞᵢ ΔΞₐ) (comb Γ:⧺ˡ Γ:⧺ʳ ΔΓᵢ ΔΓₐ)))
    (foldl ⧺₁ ΔΣ₀ ΔΣs))

  (splicing-local
      ((define undef {set -undefined})
       (define get-mt-blob : (Index → (Vectorof V^))
         (let ([cache : (Mutable-HashTable Index (Vectorof V^)) (make-hasheq)])
           (λ (n) (hash-ref! cache n (λ () ((inst make-vector V^) n ∅)))))))

    (: resolve : (U Symbol -𝒾) Σ → D)
    (define (resolve x Σ)
      (match-define (cons Ξ Γ) Σ)

      (: on-rhs : γ S → D)
      (define (on-rhs lhs rhs)
        (match rhs
          [(and alias (or (? -prim?) (? T?))) alias]
          [(== undef) undef]
          [(? set?) lhs]
          [(? α? α) (assert (car (hash-ref Ξ α)) set?)]))

      (if (symbol? x)
          (on-rhs (γ:lex x) (hash-ref Γ (γ:lex x) (λ () undef)))
          (on-rhs (γ:top x) (car (hash-ref Ξ (γ:top x) (λ () (cons undef 0)))))))

    (: Σ@ : α Σ → V^)
    (define (Σ@ α Σ) (unpack (assert (Σ@/raw α Σ) D?) Σ))

    (: Σ@/blob : α Σ → (Vectorof V^))
    (define (Σ@/blob α Σ) (assert (Σ@/raw α Σ) vector?))

    (: Σ@/env : α Σ → Γ)
    (define (Σ@/env α Σ) (assert (Σ@/raw α Σ) hash?))

    (: Σ@/raw : α Σ → S)
    (define (Σ@/raw α Σ)
      (match-define (cons Ξ Γ) Σ)
      (cond
        [(γ:lex? α) (hash-ref Γ α)]
        [(hash-ref Ξ α #f) => car]
        [(γ:imm*? α) (resolve-imm α)]
        [else
         (match α
           [(α:dyn β _)
            (match β
              [(β:st-elems _ 𝒾) (get-mt-blob (count-struct-fields 𝒾))]
              [(β:vect-elems _ n) (get-mt-blob n)]
              [(β:vect/c-elems _ n) (get-mt-blob n)]
              [(β:st/c-elems _ 𝒾) (get-mt-blob (count-struct-fields 𝒾))]
              [(β:clo _) ⊤Γ]
              [_ ∅])]
           [_ ∅])])))

  (splicing-local
      ((define cache-listof : (Mutable-HashTable γ:imm* V^) (make-hash)))
    (define resolve-imm : (case->
                           [γ:imm → V^]
                           [γ:imm* → S])
      (match-lambda
        [(γ:imm V) {set V}]
        [(γ:imm:blob S _) S]
        [(γ:imm:blob:st S _ _) S]
        [(? γ:imm:listof? α) (hash-ref! cache-listof α (λ () {set (ListOf α)}))])))

  (: unpack : D Σ → V^)
  (define (unpack D Σ)
    (: unpack-T : T* → V^)
    (define (unpack-T T)
      (cond [(T:@? T) (unpack-T:@ T)]
            [(-prim? T) {set T}]
            [(-λ? T) (assert (hash-ref (cdr Σ) T) set?)]
            [else (unpack-α T)]))

    (: unpack-α : α → V^)
    (define (unpack-α α)
      (match (Σ@/raw α Σ)
        [(? set? Vs) Vs]
        [(? α? α*) (unpack-α α*)]))

    (: unpack-T:@ : T:@ → V^)
    (define (unpack-T:@ T)
      (match T
        [(T:@ (? -st-ac? ac) (list T*))
         (for/fold ([acc : V^ ∅]) ([V (in-set (unpack-T T*))])
           (V⊔ acc (V@ ac V)))]
        [_ (hack:refine-more
            T
            (match (hash-ref (cdr Σ) T #f)
              [(? set? Vs) Vs]
              [(and T* (or (? T?) (? -prim?))) (unpack-T T*)]
              [S (error 'unpack-T:@ "~a ⊢ ~a -> ~a" (show-Σ Σ) (show-D T) (and S (show-S S)))]))]))

    (: hack:refine-more : T V^ → V^)
    ;; FIXME: will eventually be obsolete when primitive DSL allows dependency
    (define (hack:refine-more T Vs)
      (match T
        [(T:@ '* (list T* T*))
         (case (sat Σ 'real? T*)
           [(✓) (refine-V^ Vs (P:≥ 0) Σ)]
           [(#f) Vs]
           [(✗) !!!])]
        [(T:@ '+ Ts)
         (if (and (for/and : Boolean ([T (in-list Ts)])
                    (equal? '✓ (sat Σ '>= T -zero)))
                  (for/or : Boolean ([T (in-list Ts)])
                    (equal? '✓ (sat Σ '> T -zero))))
             (refine-V^ Vs (P:> 0) Σ)
             Vs)]
        [_ Vs]))

    (: V@ : -st-ac V → V^)
    (define (V@ ac V)
      (match-define (-st-ac 𝒾 i) ac)
      (match V
        [(St (and α (α:dyn (β:st-elems _ 𝒿) _)) Ps)
         #:when (𝒿 . substruct? . 𝒾)
         (define Vᵢ (vector-ref (Σ@/blob α Σ) i))
         (refine-V^ Vᵢ (ac-Ps ac Ps) Σ)]
        [(-● Ps)
         (define Ps* (ac-Ps ac Ps))
         (if (prim-struct? 𝒾)
             {set (-● Ps*)}
             (let ([Vs (unpack-α (γ:escaped-field 𝒾 i))])
               (if (set-empty? Vs) ∅ (refine-V^ Vs Ps* Σ))))]
        [_ ∅]))

    (if (set? D) D (unpack-T D)))

  (: unpack-W : W Σ → (Listof V^))
  (define (unpack-W W Σ) (map (λ ([D : D]) (unpack D Σ)) W))

  (: alloc : α S → ΔΣ)
  (define (alloc α S)
    (if (γ:lex? α)
        (if (or (set? S) (α? S)) (cons ⊥Ξ (hash α S)) !!!)
        (let ([n (if (care-if-singular? α) 1 'N)])
          (cons (hash α (cons S n)) ⊤Γ))))

  (: alloc-top : -𝒾 D → ΔΣ)
  (define (alloc-top 𝒾 V^)
    (define α (γ:top 𝒾))
    (cons (if (assignable? 𝒾)
              (let ([α* (α:dyn (β:mut 𝒾) H₀)])
                (hash α* (cons V^ 1)
                      α  (cons α* 1)))
              (hash α (cons V^ 1)))
          ⊤Γ))

  (: alloc-top* : (Listof -𝒾) W → ΔΣ)
  (define (alloc-top* xs W)
    (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([x (in-list xs)] [Vs (in-list W)])
      (⧺ ΔΣ (alloc-top x Vs))))

  (: alloc-lex : Σ Symbol D → ΔΣ)
  (define (alloc-lex Σ x V^)
    (define α (γ:lex x))
    (if (assignable? x)
        (let ([α* (α:dyn (β:mut x) H₀)])
          (cons (hash α* (cons (unpack V^ Σ) 1)) (hash α α*)))
        (cons ⊥Ξ (hash α V^))))

  (: alloc-lex* : Σ (Listof Symbol) W → ΔΣ)
  (define (alloc-lex* Σ xs W)
    (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([x (in-list xs)] [V (in-list W)])
      (⧺ ΔΣ (alloc-lex Σ x V))))

  (: alloc-vararg : Σ Symbol W → ΔΣ)
  (define (alloc-vararg Σ x W)
    (define-values (Vᵣ ΔΣ) (alloc-rest x (unpack-W W Σ)))
    (⧺ ΔΣ (alloc-lex Σ x Vᵣ)))

  (: alloc-rest ([(U Symbol ℓ) (Listof V^)] [#:tail V^] . ->* . (values V^ ΔΣ)))
  (define (alloc-rest x Wᵣ #:tail [tail {set -null}])
    (let go ([Wᵣ : (Listof V^) Wᵣ] [i : Natural 0])
      (match Wᵣ
        ['() (values tail ⊥ΔΣ)]
        [(cons Vᵢ Wᵣ*)
         (define-values (Vₜ ΔΣₜ) (go Wᵣ* (add1 i)))
         (define α (α:dyn (β:st-elems (cons x (assert i index?)) -𝒾-cons) H₀))
         (values {set (St α ∅)} (⧺ ΔΣₜ (alloc α (vector-immutable Vᵢ Vₜ))))])))

  (: mut : α S Σ → ΔΣ)
  (define (mut α S Σ)
    (define ambig?
      (case (cdr (hash-ref (car Σ) α))
        [(1) #f]
        [(N) #t]))
    (cons (hash α (cons S (if ambig? '? 0))) ⊤Γ))

  (: Γ:⧺ʳ : ΔΓ T S* → ΔΓ)
  (define (Γ:⧺ʳ ΔΓ T Vs)
    (match (hash-ref ΔΓ T #f)
      [(or (? -b?) (? T?)) ΔΓ] ; No overwriting of refinement
      [_ (hash-set ΔΓ T Vs)]))

  (: Γ:⧺ˡ : T S* ΔΓ → ΔΓ)
  (define (Γ:⧺ˡ T Vs ΔΓ)
    (define (upd) (hash-set ΔΓ T Vs))
    (match Vs
      [(or (? -b?) (? T?)) (upd)] ; prioritize refinement
      [_ (if (hash-has-key? ΔΓ T) ΔΓ (upd))]))

  (splicing-local
      ((: -S⊔ (case->
               [S* S* → S*]
               [S S → S]))
       ;; More primitive join operation that don't need store
       (define (-S⊔ S₁ S₂)
         (cond
           [(and (vector? S₁) (vector? S₂)) (vector-map V⊔ S₁ S₂)]
           [(and (hash? S₁) (hash? S₂)) (-Γ⊔ S₁ S₂)]
           [(and (set? S₁) (set? S₂)) (V⊔ S₁ S₂)]
           [else (unless (equal? S₁ S₂) !!!) S₁]))
       (: -Γ⊔ : Γ Γ → Γ)
       (define (-Γ⊔ Γ₁ Γ₂)
         (for/hash : Γ ([T (in-set (∩ (dom Γ₁) (dom Γ₂)))])
           (values T (-S⊔ (hash-ref Γ₁ T) (hash-ref Γ₂ T))))))
    (: Ξ:⧺ʳ : ΔΞ α (Pairof S N) → ΔΞ)
    ;; Apply effect to store delta as if it happened *after* the delta
    (define (Ξ:⧺ʳ ΔΞ α r₁)
      (match-define (cons S₁ N₁) r₁)
      (hash-set ΔΞ α
                (match (hash-ref ΔΞ α #f)
                  [(cons S₀ N₀)
                   (match* (N₀ N₁)
                     [((or 0 '?)  0) (cons S₁           0)]
                     [(1          0) (cons S₁           1)]
                     [((or 0 '?) '?) (cons (-S⊔ S₀ S₁) '?)]
                     [(1         '?) (cons (-S⊔ S₀ S₁)  1)]
                     [((or 0 '?)  1) (cons (-S⊔ S₀ S₁)  1)]
                     [(_          _) (cons (-S⊔ S₀ S₁) 'N)])]
                  [#f r₁])))

    (: Ξ:⧺ˡ : α (Pairof S N) Ξ → ΔΞ)
    ;; Apply effect to store delta as if it happened *before* the delta
    (define (Ξ:⧺ˡ α r₀ ΔΞ)
      (match-define (cons S₀ N₀) r₀)
      (match (hash-ref ΔΞ α #f)
        [(cons S₁ N₁)
         (match* (N₀ N₁)
           [((or 0 '?) (or 0 '?)) ΔΞ]
           [(1         (or 0 '?)) (hash-set ΔΞ α (cons S₁ 1))]
           [((or 0 '?) 1        ) (hash-set ΔΞ α (cons (-S⊔ S₀ S₁) 1))]
           [(_         _        ) (hash-set ΔΞ α (cons (-S⊔ S₀ S₁) 'N))])]
        [#f (hash-set ΔΞ α r₀)])))

  (: ΔΓ⊔ : Σ ΔΓ Σ ΔΓ → ΔΓ)
  (define (ΔΓ⊔ Σ₁ ΔΓ₁ Σ₂ ΔΓ₂)
    (for/hash : ΔΓ ([T (in-set (∩ (dom ΔΓ₁) (dom ΔΓ₂)))])
      (values T (S⊔ Σ₁ (hash-ref ΔΓ₁ T) Σ₂ (hash-ref ΔΓ₂ T)))))

  (: ΔΞ⊔ : Σ ΔΞ Σ ΔΞ → ΔΞ)
  ;; Blur store deltas. Commutative.
  (define (ΔΞ⊔ Σ₁ ΔΞ₁ Σ₂ ΔΞ₂)
    (: add-both : ΔΞ α (Pairof S N) (Pairof S N) → ΔΞ)
    (define (add-both acc α r₁ r₂)
      (match-define (cons S₁ N₁) r₁)
      (match-define (cons S₂ N₂) r₂)
      (hash-set acc α (cons (S⊔ Σ₁ S₁ Σ₂ S₂) (N-max N₁ N₂))))

    (: add-one : ΔΞ α (Pairof S N) → ΔΞ)
    (define (add-one acc α r)
      (match-define (cons S N) r)
      (case N
        ;; Turn strong to weak update
        [(0) (hash-set acc α (cons S '?))]
        [else (hash-set acc α r)]))

    (for/fold ([ΔΞ* : ΔΞ ⊥ΔΞ]) ([α (in-set (∪ (dom ΔΞ₁) (dom ΔΞ₂)))])
      (match (hash-ref ΔΞ₁ α #f)
        [(? values r₁)
         (match (hash-ref ΔΞ₂ α #f)
           [(? values r₂) (add-both ΔΞ* α r₁ r₂)]
           [#f (add-one ΔΞ* α r₁)])]
        [#f (add-one ΔΞ* α (hash-ref ΔΞ₂ α))])))

  (: ΔΣ⊔ : Σ ΔΣ ΔΣ → ΔΣ)
  (define (ΔΣ⊔ Σ ΔΣ₁ ΔΣ₂)
    (define Σ₁ (⧺ Σ ΔΣ₁))
    (define Σ₂ (⧺ Σ ΔΣ₂))
    (match-define (cons ΔΞ₁ ΔΓ₁) ΔΣ₁)
    (match-define (cons ΔΞ₂ ΔΓ₂) ΔΣ₂)
    (cons (ΔΞ⊔ Σ₁ ΔΞ₁ Σ₂ ΔΞ₂) (ΔΓ⊔ Σ₁ ΔΓ₁ Σ₂ ΔΓ₂)))

  (: S⊔ (case->
         [Σ S* Σ S* → S*]
         [Σ S Σ S → S]))
  (define (S⊔ Σ₁ S₁ Σ₂ S₂)
    (cond
      [(and (vector? S₁) (vector? S₂)) (vector-map V⊔ S₁ S₂)]
      [(and (hash? S₁) (hash? S₂)) (ΔΓ⊔ Σ₁ S₁ Σ₂ S₂)]
      [(and (set? S₁) (set? S₂)) (V⊔ S₁ S₂)]
      [(and (D? S₁) (D? S₂))
       (cond [(equal? S₁ S₂) S₁]
             [else (V⊔ (unpack S₁ Σ₁) (unpack S₂ Σ₂))])]
      [else (unless (equal? S₁ S₂) !!!) S₁]))

  (: N-max : N N → N)
  ;; Take cardinalitt max
  (define (N-max N₁ N₂)
    (cond [(or (equal? 'N N₁) (equal? 'N N₂)) 'N]
          [(or (equal? 1 N₁) (equal? 1 N₂)) 1]
          [(or (equal? '? N₁) (equal? '? N₂)) '?]
          [else 0]))

  (: ΔΣ⊕ : ΔΣ ΔΣ → (Option ΔΣ))
  (define (ΔΣ⊕ ΔΣ₁ ΔΣ₂)
    (define-type Ord (U '= '≤ '≥ #f))

    (define max-ord : (Ord Ord → Ord)
      (match-lambda**
       [(o '=) o ]
       [('= o) o ]
       [(o  o) o ]
       [(_  _) #f]))

    (define (cmp-Vs [Vs₁ : V^] [Vs₂ : V^]) : Ord
      (match* ((⊆ Vs₁ Vs₂) (⊆ Vs₂ Vs₁))
        [(#t #t) '=]
        [(#t _ ) '≤]
        [(_  #t) '≥]
        [(_  _ ) #f]))

    (define (cmp-D [D₁ : D] [D₂ : D]) : Ord
      (cond [(and (set? D₁) (set? D₂)) (cmp-Vs D₁ D₂)]
            [(equal? D₁ D₂) '=]
            [else #f]))

    (define cmp-S : (S S → Ord)
      (match-lambda**
       [((? vector? S₁) (? vector? S₂))
        (for/fold ([acc : Ord '=])
                  ([Vs₁ (in-vector S₁)] [Vs₂ (in-vector S₂)] #:break (not acc))
          (max-ord acc (cmp-Vs Vs₁ Vs₂)))]
       [((? hash? Γ₁) (? hash? Γ₂))
        (for/fold ([acc : Ord '=])
                  ([(x D₁) (in-hash Γ₁)] #:break (not acc))
          (match (hash-ref Γ₂ x #f)
            [(? values (? D? D₂)) (max-ord acc (cmp-D (assert D₁ D?) D₂))]
            [(? α? D₂) (max-ord acc (begin0 '=
                                      (assert (equal? D₁ D₂))))]
            [#f #f]))]
       [((? set? S₁) (? set? S₂))
        (cmp-Vs S₁ S₂)]
       [(S₁ S₂) (and (equal? S₁ S₂) '=)]))

    (define cmp-r : ((Pairof S N) (Pairof S N) → Ord)
      (match-lambda**
       [((cons S₁ N₁) (cons S₂ N₂)) (max-ord (cmp-S S₁ S₂) (cmp-N N₁ N₂))]))
    (define cmp-N : (N N → Ord)
      (let ([ord : (N → Index)
                 (λ (N) (case N
                          [(0) 0]
                          [(?) 1]
                          [(1) 2]
                          [(N) 3]))])
        (λ (N₁ N₂)
          (define o₁ (ord N₁))
          (define o₂ (ord N₂))
          (cond [(= o₁ o₂) '=]
                [(< o₁ o₂) '≤]
                [else '≥]))))

    (: ΔΞ⊕ : ΔΞ ΔΞ → (Option ΔΞ))
    (define (ΔΞ⊕ ΔΞ₁ ΔΞ₂)
      (cond [(= (hash-count ΔΞ₁) (hash-count ΔΞ₂))
             (define cmp
               (for/fold ([cmp : Ord '=])
                         ([(α r₁) (in-hash ΔΞ₁)] #:break (not cmp))
                 (match (hash-ref ΔΞ₂ α #f)
                   [(? values r₂) (max-ord cmp (cmp-r r₁ r₂))]
                   [#f #f])))
             (case cmp
               [(≥ =) ΔΞ₁]
               [(≤  ) ΔΞ₂]
               [else #f])]
            [else #f]))

    (: ΔΓ⊕ : ΔΓ ΔΓ → (Option ΔΓ))
    (define (ΔΓ⊕ ΔΓ₁ ΔΓ₂)
      (cond [(= (hash-count ΔΓ₁) (hash-count ΔΓ₂))
             (define cmp
               (for/fold ([cmp : Ord '=])
                         ([(x D₁) (in-hash ΔΓ₁)] #:break (not cmp))
                 (match (hash-ref ΔΓ₂ x #f)
                   [(? values D₂)
                    (if (and (D? D₁) (D? D₂))
                        (max-ord cmp (cmp-D D₁ D₂))
                        (begin0 '=
                          (assert (equal? D₁ D₂))))]
                   [#f #f])))
             (case cmp
               [(≥ =) ΔΓ₁]
               [(≤  ) ΔΓ₂]
               [else #f])]
            [else #f]))
    
    (match-define (cons ΔΞ₁ ΔΓ₁) ΔΣ₁)
    (match-define (cons ΔΞ₂ ΔΓ₂) ΔΣ₂)
    (define ΔΓ* (ΔΓ⊕ ΔΓ₁ ΔΓ₂))
    (and ΔΓ*
         (let ([ΔΞ* (ΔΞ⊕ ΔΞ₁ ΔΞ₂)])
           (and ΔΞ* (cons ΔΞ* ΔΓ*)))))

  (: ΔΣ⊔₁ : ΔΣ (℘ ΔΣ) → (℘ ΔΣ))
  (define (ΔΣ⊔₁ ΔΣ ΔΣs) (merge/compact₁ ΔΣ⊕ ΔΣ ΔΣs))

  (: collapse-ΔΣs : Σ (℘ ΔΣ) → ΔΣ)
  (define (collapse-ΔΣs Σ ΔΣs)
    (set-fold (curry ΔΣ⊔ Σ) (set-first ΔΣs) (set-rest ΔΣs)))

  (define mutable? : (α → Boolean)
    (match-lambda
      [(α:dyn β _)
       (match β
         [(or (? β:mut?) (? β:vect-elems?)) #t]
         [(β:st-elems _ 𝒾) (not (struct-all-immutable? 𝒾))]
         [_ #f])]
      [_ #f]))

  ;; HACK to reduce redundant iterations
  (: care-if-singular? : α → Boolean)
  (define (care-if-singular? α)
    (or (mutable? α)
        ;; Care if "stack addresses" are singular so we can use them as symbolic name
        ;; With current implementation, these addresses should be singular by construction
        (γ:lex? α) (γ:top? α)))

  (: S-andmap (∀ (X) (V^ → X) ((U T* α) → X) S → (U X #t)))
  (define (S-andmap on-Vs? on-T? S)
    (cond [(vector? S) (vector-andmap on-Vs? S)]
          [(hash? S) (for/fold ([acc : (U #t X) #t])
                               ([D (in-hash-values S)] #:break (not acc))
                       (if (set? D) (on-Vs? D) (on-T? D)))]
          [(set? S) (on-Vs? S)]
          [else (on-T? S)]))

  (: S-ormap (∀ (X) (V^ → X) ((U T* α) → X) S → (U X #f)))
  (define (S-ormap on-Vs? on-T? S)
    (cond [(vector? S) (vector-ormap on-Vs? S)]
          [(hash? S) (for/or : (U X #f) ([D (in-hash-values S)])
                       (if (set? D) (on-Vs? D) (on-T? D)))]
          [(set? S) (on-Vs? S)]
          [else (on-T? S)]))
  )
