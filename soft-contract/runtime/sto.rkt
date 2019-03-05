#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         racket/splicing
         set-extras
         unreachable
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
      ((define ⊥r (cons ∅ 0))
       (define undef {set -undefined})
       (define r:undef (cons undef 'N)))

    (: lookup : α Σ → V^)
    (define (lookup α Σ)
      (if (γ:imm? α)
          (resolve-imm α)
          (match (hash-ref Σ α #f)
            [(cons V^ _)
             (match V^
               [(singleton-set (? T? T)) (if (α? T) (lookup T Σ) {set T})]
               [_ (if (γ? α) {set α} V^)])]
            [#f undef])))

    (: Σ@ : α Σ → V^)
    (define (Σ@ α Σ)
      (define (on-not-found)
        (match α
          [(or (? γ:hv?)
               (? γ:escaped-field?)
               (α:dyn (? β:sealed?) _))
           ⊥r]
          [_ r:undef]))
      (if (γ:imm*? α)
          (resolve-imm α)
          (car (hash-ref Σ α on-not-found)))))

  (splicing-local
      ((define γ:null? (γ:imm 'null?))
       (define cache-listof : (Mutable-HashTable γ:imm* V^) (make-hash)))
    (define resolve-imm : (γ:imm* → V^)
      (match-lambda
        [(γ:imm V) {set V}]
        [(and α (γ:imm:listof x Cₑ ℓ))
         (hash-ref!
          cache-listof α
          (λ ()
            (define Cₚ (St/C -𝒾-cons (list (γ:imm Cₑ) (γ:imm:ref-listof x Cₑ ℓ))
                             (ℓ-with-id ℓ 'imm:pair)))
            {set (Or/C γ:null? (γ:imm Cₚ) (ℓ-with-id ℓ 'imm:or))}))]
        [(and α (γ:imm:ref-listof x Cₑ ℓ))
         (hash-ref! cache-listof α (λ () {set (X/C (γ:imm:listof x Cₑ ℓ))}))])))

  (: unpack : (U V V^) Σ → V^)
  (define (unpack Vs Σ)
    (define seen : (Mutable-HashTable α #t) (make-hash))

    (: V@ : -st-ac → V → V^)
    (define (V@ ac)
      (match-define (-st-ac 𝒾 i) ac)
      (match-lambda
        [(St (== 𝒾) αs Ps)
         (define-values (V* _)
           (refine (unpack-V^ (car (hash-ref Σ (list-ref αs i))) ∅)
                   (ac-Ps ac Ps)
                   Σ))
         ;; TODO: explicitly enforce that store delta doesn't matter in this case
         V*]
        [(-● Ps)
         (define Ps* (ac-Ps ac Ps))
         (if (prim-struct? 𝒾)
             {set (-● Ps*)}
             (let-values ([(V* _) (refine (unpack (γ:escaped-field 𝒾 i) Σ) Ps* Σ)])
               V*))]
        [_ ∅]))

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
      (cond [(hash-has-key? seen α) acc]
            [else (hash-set! seen α #t)
                  (set-fold unpack-V acc (Σ@ α Σ))]))

    (: unpack-T:@ : T:@ V^ → V^)
    (define (unpack-T:@ T acc)
      (match T
        [(T:@ (? -st-ac? ac) (list T*))
         (V⊔ acc (set-union-map (V@ ac) (unpack-T T* ∅)))]
        [_ acc]))

    (if (set? Vs) (unpack-V^ Vs ∅) (unpack-V Vs ∅)))

  (: unpack-W : W Σ → W)
  (define (unpack-W W Σ) (map (λ ([V^ : V^]) (unpack V^ Σ)) W))

  (: alloc : α V^ → ΔΣ)
  (define (alloc α V^)
    (define n (if (care-if-singular? α) 1 'N))
    (hash α (cons V^ n)))

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
    (if (null? Wᵣ)
        (values tail ⊥ΔΣ)
        (let* ([αₕ (α:dyn (β:var:car x #f) H₀)]
               [αₜ (α:dyn (β:var:cdr x #f) H₀)]
               [Vₚ (Cons αₕ αₜ)]
               [ΔΣ₀ (alloc αₜ (set-add tail Vₚ))])
          (values {set Vₚ}
                  (let loop ([Vₕ (car Wᵣ)] [Wₜ (cdr Wᵣ)] [ΔΣ : ΔΣ ΔΣ₀])
                    (define ΔΣ* (alloc-on αₕ Vₕ ΔΣ))
                    (if (null? Wₜ) ΔΣ* (loop (car Wₜ) (cdr Wₜ) ΔΣ*)))))))

  (: alloc-each : W (Natural → β) → (Values (Listof α) ΔΣ))
  (define (alloc-each Vs β-of)
    (define-values (αs:rev ΔΣ*)
      (for/fold ([αs:rev : (Listof α) '()] [ΔΣ* : ΔΣ ⊥ΔΣ])
                ([Vᵢ (in-list Vs)] [i : Natural (in-naturals)])
        (define αᵢ (α:dyn (β-of i) H₀))
        (values (cons αᵢ αs:rev) (alloc-on αᵢ Vᵢ ΔΣ*))))
    (values (reverse αs:rev) ΔΣ*))

  (: alloc-on : α V^ ΔΣ → ΔΣ)
  (define (alloc-on α V^ ΔΣ) (⧺ʳ ΔΣ α (cons V^ 1))) ; FIXME apply `care-if-singular?`

  (: resolve-lex : (U Symbol -𝒾) → α)
  (define (resolve-lex x)
    (cond [(assignable? x) (α:dyn (β:mut x) H₀)]
          [(symbol? x) (γ:lex x)]
          [else (γ:top x)])) 

  (: mut : α V^ → ΔΣ)
  (define (mut α V^) (hash α (cons V^ 0)))

  (: ⧺ʳ : ΔΣ α (Pairof V^ N) → ΔΣ)
  ;; Apply effect to store delta as if it happened *after* the delta
  (define (⧺ʳ ΔΣ α r₁)
    (match-define (cons Vs₁ N₁) r₁)
    (hash-set ΔΣ α
              (match (hash-ref ΔΣ α #f)
                [(cons Vs₀ N₀)
                 (match* (N₀ N₁)
                   [(0 0) (cons Vs₁ 0)]
                   [(0 1) (cons (V⊔ Vs₀ Vs₁) 1)]
                   [(1 0) (cons Vs₁ 1)]
                   [(_ _) (cons (V⊔ Vs₀ Vs₁) 'N)])]
                [#f r₁])))

  (: ⧺ˡ : α (Pairof V^ N) ΔΣ → ΔΣ)
  ;; Apply effect to store delta as if it happened *before* the delta
  (define (⧺ˡ α r₀ ΔΣ)
    (match-define (cons Vs₀ N₀) r₀)
    (match (hash-ref ΔΣ α #f)
      [(cons Vs₁ N₁)
       (match* (N₀ N₁)
         [(0 0) ΔΣ]
         [(0 1) (hash-set ΔΣ α (cons (V⊔ Vs₀ Vs₁) 1))]
         [(1 0) (hash-set ΔΣ α (cons Vs₁ 1))]
         [(_ _) (hash-set ΔΣ α (cons (V⊔ Vs₀ Vs₁) 'N))])]
      [#f (hash-set ΔΣ α r₀)]))

  (: ΔΣ⊔ : ΔΣ ΔΣ → ΔΣ)
  ;; Blur store deltas. Commutative.
  (define (ΔΣ⊔ ΔΣ₁ ΔΣ₂)
    (if (> (hash-count ΔΣ₁) (hash-count ΔΣ₂))
        (ΔΣ⊔ ΔΣ₂ ΔΣ₁)
        (for/fold ([ΔΣ* : ΔΣ ΔΣ₂]) ([(α r) (in-hash ΔΣ₁)])
          (⊔₁ α r ΔΣ*))))

  (: ⊔₁ : α (Pairof V^ N) ΔΣ → ΔΣ)
  ;; Blur effect in store.
  (define (⊔₁ α r ΔΣ)
    (match-define (cons Vs N) r)
    (match-define (cons Vs₀ N₀) (hash-ref ΔΣ α (λ () (cons ∅ 0))))
    (hash-set ΔΣ α (cons (V⊔ Vs₀ Vs) (N-max N₀ N))))

  (: N-max : N N → N)
  ;; Take cardinalitt max
  (define (N-max N₁ N₂)
    (cond [(or (equal? 'N N₁) (equal? 'N N₂)) 'N]
          [(or (equal? 1 N₁) (equal? 1 N₂)) 1]
          [else 0]))
  
  (: N+ : N N → N)
  ;; Add up cardinalities
  (define (N+ N₀ N₁)
    (cond [(equal? 0 N₀) N₁]
          [(equal? 0 N₁) N₀]
          [else 'N])) 

  (: stack-copy : (℘ α) Σ → ΔΣ)
  (define (stack-copy αs Σ)
    (define rn
      (for/hash : (Immutable-HashTable α γ) ([α (in-set αs)])
        (match-define (α:dyn (? symbol? x) _) α)
        (values α (γ:lex x))))
    (copy/rename rn Σ))

  (: escape : (℘ Symbol) Σ → (Values (℘ α) ΔΣ))
  (define (escape Xs Σ)
    (define rn (for/hash : (Immutable-HashTable γ α) ([x (in-set Xs)])
                 (values (γ:lex x) (α:dyn x H₀))))
    (values (list->set (hash-values rn)) (copy/rename rn Σ)))

  (: copy/rename : (Immutable-HashTable α α) Σ → Σ)
  (define (copy/rename rn Σ₀)
    (define adjust : (case-> [α → α]
                             [T → T]
                             [(U T -b) → (U T -b)])
      (let ([f (rename rn)])
        (λ (T)
          (define T* (f T))
          (if (α? T) (assert T* α?) (assert T*)))))
    (define (go-V^ [V^ : V^]) (map/set go-V V^))
    (define go-V : (V → V)
      (match-lambda
        [(? T? T) (go-T T)]
        [(-● Ps) (-● (map/set go-P Ps))]
        [(St 𝒾 αs Ps) (St 𝒾 αs (map/set go-P Ps))]
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
      (define Vs (car r))
      (cond [(hash-ref rn α #f) => (λ (α*) (⧺ acc (alloc α* (go-V^ Vs))))]
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

  (define mutable? : (α → Boolean)
    (match-lambda
      [(α:dyn β _)
       (match β
         [(? β:mut?) #t]
         [(β:fld 𝒾 _ i) (struct-mutable? 𝒾 i)]
         [_ #f])]
      [(? γ:escaped-field?) #t]
      [_ #f]))

  ;; HACK to reduce redundant iterations
  (define care-if-singular? : (α → Boolean)
    (match-lambda
      ;; Care if mutable addreses are singular so we can do strong update
      [(α:dyn β _)
       (match β
         [(or (? β:mut?) (? β:idx?)) #t]
         [(β:fld 𝒾 _ i) (struct-mutable? 𝒾 i)]
         [_ #f])]
      ;; Care if "stack addresses" are singular so we can use them as symbolic name
      ;; With current implementation, these addresses should be singular by construction
      [(or (? γ:lex?) (? γ:top?) (? γ:wrp?)) #t]
      [_ #f]))
  )
