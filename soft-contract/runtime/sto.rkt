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

  (: ⧺ : ΔΣ * → ΔΣ)
  ;; Combine store deltas. *Not* commutative due to strong updates when possible.
  ;; (A store is a special case of store-delta where the cardinality is positive)
  (define (⧺ . ΔΣs)
    (define (⧺₁ [ΔΣᵢ : ΔΣ] [acc : ΔΣ])
      (if (> (hash-count acc) (hash-count ΔΣᵢ))
          (for/fold ([acc : ΔΣ acc]) ([(α rᵢ) (in-hash ΔΣᵢ)])
            (⧺ʳ acc α rᵢ))
          (for/fold ([ΔΣᵢ : ΔΣ ΔΣᵢ]) ([(α r₀) (in-hash acc)])
            (⧺ˡ α r₀ ΔΣᵢ))))
    (foldl ⧺₁ ⊥ΔΣ ΔΣs))

  (: lookup : (U T:@ α) Σ → V^)
  (define (lookup T Σ)
    (match (hash-ref Σ T #f)
      [(cons V^ _)
       (match V^
         [(singleton-set (and T* (or (? T:@?) (? α?)))) (lookup T* Σ)]
         [_ (cond [(and (α? T) (mutable? T)) V^]
                  [(or (γ? T) (T:@? T)) {set T}]
                  [else V^])])]
      [#f (if (T:@? T) ; paths are fine
              {set T}
              (error 'lookup "nothing at ~a in ~a" T (show-Σ Σ)))]))

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

  (: unalloc-prefix : Natural V^ Σ → (Option (Pairof W V^)))
  ;; Extract list of `n` values out of `V` representing a value list
  (define (unalloc-prefix n Vᵣ Σ)
    (define ● (-● ∅))
    (let go ([n : Integer n] [rev-W : W '()] [Vᵣ : V^ Vᵣ])
      (if (<= n 0)
          (cons (reverse rev-W) Vᵣ)
          (let-values ([(Vₕ Vₜ er?)
                        (for/fold ([Vₕ : V^ ∅] [Vₜ : V^ ∅] [er? : Boolean #f])
                                  ([Vᵢ (in-set Vᵣ)] #:unless #f)
                          (match Vᵢ
                            [(Cons αₕ αₜ)
                             (values (∪ Vₕ (unpack αₕ Σ)) (∪ Vₜ (unpack αₜ Σ)) #t)]
                            [(-● Ps)
                             #:when (∋ Ps 'list?)
                             (values (set-add Vₕ ●) (set-add Vₜ (-● {set 'list?})) #t)]
                            [(Guarded-Cons α) ???]
                            [_ (values ∅ ∅ #f)]))])
            (and (not er?) (go (- n 1) (cons Vₕ rev-W) Vₜ))))))

  (: resolve-lex : (U Symbol -𝒾) → α)
  (define (resolve-lex x)
    (cond [(assignable? x) (α:dyn (β:mut x) H₀)]
          [(symbol? x) (γ:lex x)]
          [else (γ:top x)]))

  (define n : Natural 0)
  
  (: unpack : (U T:@ α V^) Σ → V^)
  (define (unpack Vs Σ)
    (define seen : (Mutable-HashTable T #t) (make-hash))
    (set! n (+ 1 n))
    (when (> n 1000)
      (error 'stopped))

    (: V@ : -st-ac → V → V^)
    (define (V@ ac)
      (match-define (-st-ac 𝒾 i) ac)
      (match-lambda
        [(St (== 𝒾) αs) (unpack-V^ (car (hash-ref Σ (list-ref αs i))) ∅)]
        [(-● _) {set (-● ∅)}]
        [_ ∅]))

    (: unpack-V : V V^ → V^)
    (define (unpack-V V acc)
      (if (or (T:@? V) (α? V)) (unpack-T V acc) (set-add acc V)))

    (: unpack-V^ : V^ V^ → V^)
    (define (unpack-V^ Vs acc) (set-fold unpack-V acc Vs))

    (: unpack-T : (U T:@ α) V^ → V^)
    (define (unpack-T T acc)
      (cond [(γ:imm? T) (set-add acc (γ:imm-_0 T))]
            [(hash-has-key? seen T) acc]
            [else (hash-set! seen T #t)
                  (match (hash-ref Σ T #f)
                    [(cons Vs _) (set-fold unpack-V acc Vs)]
                    [#f
                     (match T
                       [(T:@ (? -st-ac? ac) (list (and T* (or (? T:@?) (? α?)))))
                        (∪ acc (set-union-map (V@ ac) (unpack-T T* ∅)))]
                       [(? T:@?) (set-add acc (-● ∅))]
                       [(? α?) (error 'unpack-T "no ~a" T)])])]))

    (if (set? Vs) (unpack-V^ Vs ∅) (unpack-T Vs ∅)))

  (: unpack-W : W Σ → W)
  (define (unpack-W W Σ) (map (λ ([V^ : V^]) (unpack V^ Σ)) W))

  (: mut : (U α T:@) V^ → ΔΣ)
  (define (mut T V^) (hash T (cons V^ 0))) 

  (: ⧺ʳ : ΔΣ T (Pairof V^ N) → ΔΣ)
  ;; Apply effect to store delta as if it happened *after* the delta
  (define (⧺ʳ ΔΣ T r₁)
    (match-define (cons Vs₁ N₁) r₁)
    (hash-set ΔΣ T
              (match (hash-ref ΔΣ T #f)
                [(cons Vs₀ N₀)
                 (match* (N₀ N₁)
                   [(0 0) (cons Vs₁ 0)]
                   [(0 1) (cons (∪ Vs₀ Vs₁) 1)]
                   [(1 0) (cons Vs₁ 1)]
                   [(_ _) (cons (∪ Vs₀ Vs₁) 'N)])]
                [#f r₁])))

  (: ⧺ˡ : T (Pairof V^ N) ΔΣ → ΔΣ)
  ;; Apply effect to store delta as if it happened *before* the delta
  (define (⧺ˡ T r₀ ΔΣ)
    (match-define (cons Vs₀ N₀) r₀)
    (match (hash-ref ΔΣ T #f)
      [(cons Vs₁ N₁)
       (match* (N₀ N₁)
         [(0 0) ΔΣ]
         [(0 1) (hash-set ΔΣ T (cons (∪ Vs₀ Vs₁) 1))]
         [(1 0) (hash-set ΔΣ T (cons Vs₁ 1))]
         [(_ _) (hash-set ΔΣ T (cons (∪ Vs₀ Vs₁) 'N))])]
      [#f (hash-set ΔΣ T r₀)]))

  (: ΔΣ⊔ : ΔΣ ΔΣ → ΔΣ)
  ;; Blur store deltas. Commutative.
  (define (ΔΣ⊔ ΔΣ₁ ΔΣ₂)
    (if (> (hash-count ΔΣ₁) (hash-count ΔΣ₂))
        (ΔΣ⊔ ΔΣ₂ ΔΣ₁)
        (for/fold ([ΔΣ* : ΔΣ ΔΣ₂]) ([(α r) (in-hash ΔΣ₁)])
          (⊔₁ α r ΔΣ*))))

  (: ⊔₁ : T (Pairof V^ N) ΔΣ → ΔΣ)
  ;; Blur effect in store.
  (define (⊔₁ T r ΔΣ)
    (match-define (cons Vs N) r)
    (match-define (cons Vs₀ N₀) (hash-ref ΔΣ T (λ () (cons ∅ 0))))
    (hash-set ΔΣ T (cons (∪ Vs₀ Vs) (N-max N₀ N))))

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

  (: close : Σ (℘ Symbol) → (Values (℘ α) ΔΣ))
  (define (close Σ Xs)
    (for/fold ([xs* : (℘ α) ∅] [ΔΣ : ΔΣ ⊥ΔΣ]) ([x (in-set Xs)])
      (define x* (α:dyn x H₀))
      (values (set-add xs* x*) (⧺ ΔΣ (alloc x* (unpack (γ:lex x) Σ))))))

  (: stack-copy : (℘ α) Σ → ΔΣ)
  (define (stack-copy αs Σ)
    (for/hash : ΔΣ ([α (in-set αs)])
      (match-define (cons T _) (hash-ref Σ α (λ () (error 'stack-copy "nothing at ~a" α))))
      (match-define (α:dyn (? symbol? x) _) α)
      (values (γ:lex x) (cons T 1)))) 

  (: ambiguous? : T Σ → Boolean)
  ;; Check if identity `T` is ambiguous under store `Σ`
  (define (ambiguous? T₀ Σ)
    (let go ([T : T T₀])
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
      [_ #f]))
  )
