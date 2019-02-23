#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         set-extras
         unreachable
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit sto@
  (import static-info^
          val^ pretty-print^)
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

  (: lookup : α Σ → V^)
  (define (lookup α Σ)
    (match (hash-ref Σ α #f)
      [(cons V^ _)
       (match V^
         [(singleton-set (? T? T)) (if (α? T) (lookup T Σ) {set T})]
         [_ (if (γ? α) {set α} V^)])]
      [#f (error 'lookup "nothing at ~a in ~a" (show-α α) (show-Σ Σ))]))

  (: Σ@ : α Σ → V^)
  (define (Σ@ α Σ)
    (match α
      [(γ:imm V) {set V}]
      [else (car (hash-ref Σ α (λ () (error 'Σ@ "nothing at ~a" (show-α α)))))]))

  (: alloc : α V^ → ΔΣ)
  (define (alloc α V^)
    (define n (if (γ:hv? α) 'N 1)) ; HACK to reduce redundant work
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
  (define (alloc-on α V^ ΔΣ) (⧺ʳ ΔΣ α (cons V^ 1))) 

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
                   [(0 1) (cons (∪ Vs₀ Vs₁) 1)]
                   [(1 0) (cons Vs₁ 1)]
                   [(_ _) (cons (∪ Vs₀ Vs₁) 'N)])]
                [#f r₁])))

  (: ⧺ˡ : α (Pairof V^ N) ΔΣ → ΔΣ)
  ;; Apply effect to store delta as if it happened *before* the delta
  (define (⧺ˡ α r₀ ΔΣ)
    (match-define (cons Vs₀ N₀) r₀)
    (match (hash-ref ΔΣ α #f)
      [(cons Vs₁ N₁)
       (match* (N₀ N₁)
         [(0 0) ΔΣ]
         [(0 1) (hash-set ΔΣ α (cons (∪ Vs₀ Vs₁) 1))]
         [(1 0) (hash-set ΔΣ α (cons Vs₁ 1))]
         [(_ _) (hash-set ΔΣ α (cons (∪ Vs₀ Vs₁) 'N))])]
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
    (hash-set ΔΣ α (cons (∪ Vs₀ Vs) (N-max N₀ N))))

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
    (define adjust (rename rn))
    (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([(T r) (in-hash Σ)])
      (define V^ (car r))
      (match T
        [(and (? α? α) (app (λ (α) (hash-ref rn α #f)) (? values γ)))
         (hash-set ΔΣ γ (cons V^ 1))]
        [(? T:@?) #:when (⊆ (T-root T) αs)
         (hash-set ΔΣ (assert (adjust T)) (cons V^ 0))]
        [_ ΔΣ])))

  (: ambiguous? : T Σ → Boolean)
  ;; Check if identity `T` is ambiguous under store `Σ`
  (define (ambiguous? T₀ Σ)
    (let go ([T : (U T -b) T₀])
      (cond [(-b? T) #f]
            [(T:@? T) (ormap go (T:@-_1 T))]
            [else (case (cdr (hash-ref Σ T))
                    [(1) #f]
                    [(N) #t])]))) 

  (: mutable? : α → Boolean)
  (define mutable?
    (match-lambda
      [(α:dyn β _)
       (match β
         [(? β:mut?) #t]
         [(β:fld 𝒾 _ i) (struct-mutable? 𝒾 i)]
         [_ #f])]
      [(? γ:escaped-field?) #t]
      [_ #f]))
  )
