#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         racket/vector
         racket/splicing
         set-extras
         unreachable
         (only-in "../utils/map.rkt" dom)
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
    (define (⧺₁ [ΔΣᵢ : ΔΣ] [acc : ΔΣ])
      (if (> (hash-count acc) (hash-count ΔΣᵢ))
          (for/fold ([acc : ΔΣ acc]) ([(α rᵢ) (in-hash ΔΣᵢ)])
            (⧺ʳ acc α rᵢ))
          (for/fold ([ΔΣᵢ : ΔΣ ΔΣᵢ]) ([(α r₀) (in-hash acc)])
            (⧺ˡ α r₀ ΔΣᵢ))))
    (foldl ⧺₁ ΔΣ₀ ΔΣs))
  (splicing-local
      ((define undef {set -undefined})
       (define get-mt-blob : (Index → (Vectorof V^))
         (let ([cache : (Mutable-HashTable Index (Vectorof V^)) (make-hasheq)])
           (λ (n) (hash-ref! cache n (λ () ((inst make-vector V^) n ∅)))))))

    (: lookup : γ Σ → V^)
    (define (lookup γ Σ)
      (let go ([α : α γ])
        (match (hash-ref Σ α #f)
          [(cons S _)
           (match S
             [(singleton-set (? T? T)) (if (α? T) (go T) {set T})]
             [(? set?) (if (γ? α) {set α} S)]
             [_ !!!])]
          [#f (if (γ:imm? α) (resolve-imm α) (begin (printf "undef ~a~n" (show-α γ)) undef))])))

    (: Σ@ : α Σ → V^)
    (define (Σ@ α Σ) (assert (Σ@/raw α Σ) set?))

    (: Σ@/blob : α Σ → (Vectorof V^))
    (define (Σ@/blob α Σ) (assert (Σ@/raw α Σ) vector?))

    (: Σ@/raw : α Σ → S)
    (define (Σ@/raw α Σ)
      (cond
        [(hash-ref Σ α #f) => car]
        [(γ:imm*? α) (resolve-imm α)]
        [else
         (match α
           [(α:dyn β _)
            (match β
              [(β:st-elems _ 𝒾) (get-mt-blob (count-struct-fields 𝒾))]
              [(β:vect-elems _ n) (get-mt-blob n)]
              [(β:vect/c-elems _ n) (get-mt-blob n)]
              [(β:st/c-elems _ 𝒾) (get-mt-blob (count-struct-fields 𝒾))]
              [_ ∅])]
           [_ ∅])])))

  (splicing-local
      ((define γ:null? (γ:imm 'null?))
       (define cache-listof : (Mutable-HashTable γ:imm* V^) (make-hash)))
    (define resolve-imm : (case->
                           [γ:imm → V^]
                           [γ:imm* → S])
      (match-lambda
        [(γ:imm V) {set V}]
        [(γ:imm:blob S _) S]
        [(γ:imm:blob:st S _ _) S]
        [(and α (γ:imm:listof x Cₑ ℓ))
         (hash-ref!
          cache-listof α
          (λ ()
            (define Cₚ (St/C (γ:imm:blob:st (vector-immutable {set Cₑ} {set (X/C α)})
                                            (ℓ-with-id ℓ 'imm:pair)
                                            -𝒾-cons)))
            {set (Or/C γ:null? (γ:imm Cₚ) (ℓ-with-id ℓ 'imm:or))}))])))

  (: unpack : (U V V^) Σ → V^)
  (define (unpack Vs Σ)
    (define-set seen : α)

    (: unpack-V : V V^ → V^)
    (define (unpack-V V acc) (if (T? V) (unpack-T V acc) (V⊔₁ V acc)))

    (: unpack-V^ : V^ V^ → V^)
    (define (unpack-V^ Vs acc) (set-fold unpack-V acc Vs))

    (: unpack-T : (U T -b) V^ → V^)
    (define (unpack-T T acc)
      (cond [(T:@? T) (unpack-T:@ T acc)]
            [(-b? T) (V⊔₁ T acc)]
            [else (unpack-α T acc)]))

    (: unpack-α : α V^ → V^)
    (define (unpack-α α acc)
      (cond [(seen-has? α) acc]
            [else (seen-add! α)
                  (set-fold unpack-V acc (Σ@ α Σ))]))

    (: unpack-T:@ : T:@ V^ → V^)
    (define (unpack-T:@ T acc)
      (match T
        [(T:@ (? -st-ac? ac) (list T*))
         (V⊔ acc (set-union-map (λ ([V : V]) (V@ Σ ac V)) (unpack-T T* ∅)))]
        [_ acc]))

    (if (set? Vs) (unpack-V^ Vs ∅) (unpack-V Vs ∅)))

  (: V@ : Σ -st-ac V → V^)
  (define (V@ Σ ac V)
    (match-define (-st-ac 𝒾 i) ac)
    (match V
      [(St (and α (α:dyn (β:st-elems _ (== 𝒾)) _)) Ps)
       (define Vᵢ (vector-ref (Σ@/blob α Σ) i))
       (define-values (V* _) (refine (unpack Vᵢ Σ) (ac-Ps ac Ps) Σ))
       ;; TODO: explicitly enforce that store delta doesn't matter in this case
       V*]
      [(-● Ps)
       (define Ps* (ac-Ps ac Ps))
       (if (prim-struct? 𝒾)
           {set (-● Ps*)}
           (let ([Vs (unpack (γ:escaped-field 𝒾 i) Σ)])
             (if (set-empty? Vs)
                 ∅
                 (let-values ([(Vs* _) (refine Vs Ps* Σ)])
                   Vs*))))]
      [_ ∅]))

  (: unpack-W : W Σ → W)
  (define (unpack-W W Σ) (map (λ ([V^ : V^]) (unpack V^ Σ)) W))

  (: alloc : α S → ΔΣ)
  (define (alloc α S)
    (define n (if (care-if-singular? α) 1 'N))
    (hash α (cons S n)))

  (: alloc-lex : (U Symbol -𝒾) V^ → ΔΣ)
  (define (alloc-lex x V^)
    (define α* (if (symbol? x) (γ:lex x) (γ:top x)))
    (if (assignable? x)
        (let ([α (resolve-lex x)])
          (alloc-on α V^ (alloc α* {set α})))
        (alloc α* V^)))

  (: alloc-lex* : (Listof (U Symbol -𝒾)) W → ΔΣ)
  (define (alloc-lex* xs W)
    (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([x (in-list xs)] [V (in-list W)])
      (⧺ ΔΣ (alloc-lex x V))))

  (: alloc-vararg : Symbol W → ΔΣ)
  (define (alloc-vararg x W)
    (define-values (Vᵣ ΔΣ) (alloc-rest x W))
    (⧺ ΔΣ (alloc-lex x Vᵣ)))

  (: alloc-rest ([(U Symbol ℓ) W] [#:tail V^] . ->* . (values V^ ΔΣ)))
  (define (alloc-rest x Wᵣ #:tail [tail {set -null}])
    (let go ([Wᵣ : W Wᵣ] [i : Natural 0])
      (match Wᵣ
        ['() (values tail ⊥ΔΣ)]
        [(cons Vᵢ Wᵣ*)
         (define-values (Vₜ ΔΣₜ) (go Wᵣ* (add1 i)))
         (define α (α:dyn (β:st-elems (cons x (assert i index?)) -𝒾-cons) H₀))
         (values {set (St α ∅)} (⧺ ΔΣₜ (alloc α (vector-immutable Vᵢ Vₜ))))])))

  (: alloc-on : α V^ ΔΣ → ΔΣ)
  (define (alloc-on α V^ ΔΣ) (⧺ʳ ΔΣ α (cons V^ 1))) ; FIXME apply `care-if-singular?`

  (: resolve-lex : (U Symbol -𝒾) → α)
  (define (resolve-lex x)
    (cond [(assignable? x) (α:dyn (β:mut x) H₀)]
          [(symbol? x) (γ:lex x)]
          [else (γ:top x)])) 

  (: mut : α S Σ → ΔΣ)
  (define (mut α S Σ) (hash α (cons S (if (ambiguous? α Σ) '? 0))))

  (: ⧺ʳ : ΔΣ α (Pairof S N) → ΔΣ)
  ;; Apply effect to store delta as if it happened *after* the delta
  (define (⧺ʳ ΔΣ α r₁)
    (match-define (cons S₁ N₁) r₁)
    (hash-set ΔΣ α
              (match (hash-ref ΔΣ α #f)
                [(cons S₀ N₀)
                 (match* (N₀ N₁)
                   [((or 0 '?)  0) (cons S₁           0)]
                   [(1          0) (cons S₁           1)]
                   [((or 0 '?) '?) (cons (S⊔ S₀ S₁) '?)]
                   [(1         '?) (cons (S⊔ S₀ S₁)  1)]
                   [((or 0 '?)  1) (cons (S⊔ S₀ S₁)  1)]
                   [(_          _) (cons (S⊔ S₀ S₁) 'N)])]
                [#f r₁])))

  (: ⧺ˡ : α (Pairof S N) ΔΣ → ΔΣ)
  ;; Apply effect to store delta as if it happened *before* the delta
  (define (⧺ˡ α r₀ ΔΣ)
    (match-define (cons S₀ N₀) r₀)
    (match (hash-ref ΔΣ α #f)
      [(cons S₁ N₁)
       (match* (N₀ N₁)
         [((or 0 '?) (or 0 '?)) ΔΣ]
         [(1         (or 0 '?)) (hash-set ΔΣ α (cons S₁ 1))]
         [((or 0 '?) 1        ) (hash-set ΔΣ α (cons (S⊔ S₀ S₁) 1))]
         [(_         _        ) (hash-set ΔΣ α (cons (S⊔ S₀ S₁) 'N))])]
      [#f (hash-set ΔΣ α r₀)]))

  (: ΔΣ⊔ : ΔΣ ΔΣ → ΔΣ)
  ;; Blur store deltas. Commutative.
  (define (ΔΣ⊔ ΔΣ₁ ΔΣ₂)
    (: add-both : ΔΣ α (Pairof S N) (Pairof S N) → ΔΣ)
    (define (add-both acc α r₁ r₂)
      (match-define (cons S₁ N₁) r₁)
      (match-define (cons S₂ N₂) r₂)
      (hash-set acc α (cons (S⊔ S₁ S₂) (N-max N₁ N₂))))

    (: add-one : ΔΣ α (Pairof S N) → ΔΣ)
    (define (add-one acc α r)
      (match-define (cons S N) r)
      (case N
        [(0)
         ;; Either drop refinement for immutable address or
         ;; turn strong to weak update for mutable address
         (if (mutable? α) (hash-set acc α (cons S '?)) acc)]
        [else (hash-set acc α r)]))

    (for/fold ([ΔΣ* : ΔΣ ⊥ΔΣ]) ([α (in-set (∪ (dom ΔΣ₁) (dom ΔΣ₂)))])
      (match (hash-ref ΔΣ₁ α #f)
        [(? values r₁)
         (match (hash-ref ΔΣ₂ α #f)
           [(? values r₂) (add-both ΔΣ* α r₁ r₂)]
           [#f (add-one ΔΣ* α r₁)])]
        [#f (add-one ΔΣ* α (hash-ref ΔΣ₂ α))])))

  (define S⊔ : (S S → S)
    (match-lambda**
     [((? vector? Vs₁) (? vector? Vs₂)) (vector-map V⊔ Vs₁ Vs₂)]
     [((? set? Vs₁) (? set? Vs₂)) (V⊔ Vs₁ Vs₂)]))

  (: N-max : N N → N)
  ;; Take cardinalitt max
  (define (N-max N₁ N₂)
    (cond [(or (equal? 'N N₁) (equal? 'N N₂)) 'N]
          [(or (equal? 1 N₁) (equal? 1 N₂)) 1]
          [(or (equal? '? N₁) (equal? '? N₂)) '?]
          [else 0]))

  (: stack-copy : (℘ α) Σ → ΔΣ)
  (define (stack-copy αs Σ)
    (define rn
      (for/hash : (Immutable-HashTable α γ) ([α (in-set αs)])
        (match-define (α:dyn (? symbol? x) _) α)
        (values α (γ:lex x))))
    (copy/rename rn Σ))

  (: escape : (℘ Symbol) Σ → ΔΣ)
  (define (escape Xs Σ)
    (define rn (for/hash : (Immutable-HashTable γ α) ([x (in-set Xs)])
                 (values (γ:lex x) (α:dyn x H₀))))
    (copy/rename rn Σ))

  (: copy/rename : (Immutable-HashTable α α) Σ → Σ)
  (define (copy/rename rn Σ₀)
    (define adjust : (case-> [α → α]
                             [T → T]
                             [(U T -b) → (U T -b)])
      (let ([f (rename rn)])
        (λ (T)
          (define T* (f T))
          (if (α? T) (assert T* α?) (assert T*)))))
    (define (go-S [S : S]) (if (vector? S) (vector-map go-V^ S) (go-V^ S)))
    (define (go-V^ [V^ : V^]) (map/set go-V V^))
    (define go-V : (V → V)
      (match-lambda
        [(? T? T) (go-T T)]
        [(-● Ps) (-● (map/set go-P Ps))]
        [(St α Ps) (St α (map/set go-P Ps))]
        [V V]))
    (define go-P : (P → P)
      (match-lambda
        [(P:¬ Q) (P:¬ (go-Q Q))]
        [(P:St acs P) (P:St acs (go-P P))]
        [(? Q? Q) (go-Q Q)]))
    (define go-Q : (Q → Q)
      (match-lambda
        [(P:> T) (P:> (adjust T))]
        [(P:≥ T) (P:≥ (adjust T))]
        [(P:< T) (P:< (adjust T))]
        [(P:≤ T) (P:≤ (adjust T))]
        [(P:= T) (P:= (adjust T))]
        [(P:≡ T) (P:≡ (adjust T))]
        [Q Q]))
    (define (go-T [T : T]) (cond [(adjust T) => values] [else T]))
    (for/fold ([acc : ΔΣ ⊥ΔΣ]) ([(α r) (in-hash Σ₀)])
      (define S (car r))
      (cond [(hash-ref rn α #f) => (λ (α*) (⧺ acc (alloc α* (go-S S))))]
            [else acc])))

  (: ambiguous? : T Σ → Boolean)
  ;; Check if identity `T` is ambiguous under store `Σ`
  (define (ambiguous? T₀ Σ)
    (let go ([T : (U T -b) T₀])
      (cond [(-b? T) #f]
            [(T:@? T) (ormap go (T:@-_1 T))]
            [else (case (cdr (hash-ref Σ T))
                    [(1) #f]
                    [(N) #t])])))

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

    (define cmp-S : (S S → Ord)
      (match-lambda**
       [((? vector? S₁) (? vector? S₂))
        (for/fold ([acc : Ord '=])
                  ([Vs₁ (in-vector S₁)] [Vs₂ (in-vector S₂)] #:break (not acc))
          (max-ord acc (cmp-Vs Vs₁ Vs₂)))]
       [((? set? S₁) (? set? S₂))
        (cmp-Vs S₁ S₂)]))

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
    (cond [(= (hash-count ΔΣ₁) (hash-count ΔΣ₂))
           (define cmp
             (for/fold ([cmp : Ord '=])
                       ([(α r₁) (in-hash ΔΣ₁)] #:break (not cmp))
               (match (hash-ref ΔΣ₂ α #f)
                 [(? values r₂) (max-ord cmp (cmp-r r₁ r₂))]
                 [#f #f])))
           (case cmp
             [(≥ =) ΔΣ₁]
             [(≤  ) ΔΣ₂]
             [else #f])]
          [else #f]))

  (: ΔΣ⊔₁ : ΔΣ (℘ ΔΣ) → (℘ ΔΣ))
  (define (ΔΣ⊔₁ ΔΣ ΔΣs) (merge/compact₁ ΔΣ⊕ ΔΣ ΔΣs))

  (: collapse-ΔΣs : (℘ ΔΣ) → ΔΣ)
  (define (collapse-ΔΣs ΔΣs)
    (set-fold ΔΣ⊔ (set-first ΔΣs) (set-rest ΔΣs)))

  (define mutable? : (α → Boolean)
    (match-lambda
      [(α:dyn β _)
       (match β
         [(or (? β:mut?) (? β:vect-elems?)) #t]
         [(β:st-elems _ 𝒾) (not (struct-all-immutable? 𝒾))]
         [_ #f])]
      [(? γ:escaped-field?) #t]
      [_ #f]))

  ;; HACK to reduce redundant iterations
  (: care-if-singular? : α → Boolean)
  (define (care-if-singular? α)
    (or (mutable? α)
        ;; Care if "stack addresses" are singular so we can use them as symbolic name
        ;; With current implementation, these addresses should be singular by construction
        (γ:lex? α) (γ:top? α)))
  )
