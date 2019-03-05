#lang typed/racket/base

(provide exec@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         set-extras
         unreachable
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "evl.rkt"
         "app.rkt"
         "mon.rkt"
         "hv.rkt"
         "gc.rkt"
         )

(define-unit fix@
  (import static-info^
          sto^ cache^ val^
          evl^
          prover^)
  (export exec^)

  (define ⊥A : (Pairof R (℘ Err)) (cons ⊥R ∅))
  (define $ᵢₙ  : $ (⊥$))
  (define $ₒᵤₜ : $ (⊥$)) ; TODO strange that set! below complains without ann
  (define db:iter? ((inst make-parameter Boolean) #f))
  (define db:max-steps ((inst make-parameter (Option Index)) #f))
  (define db:depth ((inst make-parameter Natural) 0))
  (define current-module ((inst make-parameter -l) 'scv))

  (: exec : (U -prog E) → (Values (℘ Err) $))
  (define (exec p)
    (define run (if (-prog? p)
                    (λ () (let-values ([(_ es) (evl-prog p)]) es))
                    (λ () (let-values ([(_ es) (evl ⊥Σ p)]) es))))
    (define dump-iter? (db:iter?)) 
    (define iter : Natural 0)
    (define done? : (→ Boolean)
      (match (db:max-steps)
        [(? values n) (λ () (>= iter n))]
        [#f (λ () #f)]))
    
    (let loop ()
      (set! $ᵢₙ $ₒᵤₜ)
      (set! $ₒᵤₜ (⊥$))
      (when dump-iter?
        (printf "iter: ~a (~a) ~n" iter (hash-count $ᵢₙ)))
      (set! iter (+ 1 iter))
      (define es (run))
      (if (or (done?) (equal? $ᵢₙ $ₒᵤₜ))
          (values (set-filter blame-on-transparent? es) $ᵢₙ)
          (loop))))

  (: ref-$! : $:Key (→ (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (ref-$! key comp)
    (match (hash-ref $ₒᵤₜ key #f)
      [(cons r es) (values r es)]
      [#f
       (hash-set! $ₒᵤₜ key (hash-ref $ᵢₙ key (λ () ⊥A)))
       (define-values (r es) (comp))
       ($⊔! $ₒᵤₜ key r es)
       (values r es)]))

  (: just ([(U V V^ W)] [ΔΣ] . ->* . (Values R (℘ Err))))
  (define (just V [ΔΣ ⊥ΔΣ]) (values (R-of V ΔΣ) ∅))

  (: err ((U (℘ Err) Err) → (Values R (℘ Err))))
  (define (err er) (values ⊥R (if (set? er) er {set er})))

  (: blm : -l ℓ ℓ W W → (℘ Blm))
  (define (blm l+ ℓ ℓₒ ctc val)
    (if (transparent-module? l+) {set (Blm l+ ℓ ℓₒ ctc val)} ∅))

  (: fix-return : Renamings Σ R → R)
  (define (fix-return rn Σ₀ r)
    (define Σₑᵣ ((inst make-parameter Σ) Σ₀)) ; HACK to reduce cluttering
    (define adjust-T (rename rn))
    (define (go-ΔΣ [ΔΣ₀ : ΔΣ])
      (for*/hash : ΔΣ ([(α r) (in-hash ΔΣ₀)]
                       [α* (in-value (adjust-T α))]
                       ;; TODO generalize this
                       #:when (α? α*))
        (values α* (cons (go-V^ (car r))
                         ;; if `α` is new allocation within callee and
                         ;; `α*` is existing address, store-delta entry for `α*`
                         ;; should always be refinement,
                         ;; so should not increase cardinality
                         (if (hash-has-key? rn α) 0 (cdr r))))))
    (define (go-W [W : W]) (map go-V^ W))
    (define (go-V^ [V^ : V^]) (set-union-map go-V V^))
    (define (go-V [V : V]) (if (T? V) (go-T V) {set V}))
    (define (go-T [T : T]) (cond [(adjust-T T) => set]
                                 [else (unpack T (Σₑᵣ))]))

    (for/fold ([acc : R ⊥R]) ([(ΔΣ Ws) (in-hash r)])
      (parameterize ([Σₑᵣ (⧺ Σ₀ ΔΣ)])
        (hash-update acc
                     (go-ΔΣ ΔΣ)
                     (λ ([Ws₀ : (℘ W)]) (∪ Ws₀ (map/set go-W Ws)))
                     mk-∅))))

  (: fold-ans (∀ (X) (X → (Values R (℘ Err))) (℘ X) → (Values R (℘ Err))))
  (define (fold-ans on-X Xs)
    (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([X (in-set Xs)])
      (define-values (r* es*) (on-X X))
      (values (m⊔ r r*) (∪ es es*))))

  (: ans-map : (ΔΣ W^ → (Values R (℘ Err))) R → (Values R (℘ Err)))
  (define (ans-map on-ans r)
    (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([(ΔΣ Ws) (in-hash r)])
      (define-values (r* es*) (on-ans ΔΣ Ws))
      (values (m⊔ r r*) (∪ es es*))))

  (: with-split-Σ : Σ V W (W ΔΣ → (Values R (℘ Err))) (W ΔΣ → (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (with-split-Σ Σ P W on-t on-f)
    (define-values (W-ΔΣ:t W-ΔΣ:f) (check-plaus Σ P W))
    (define-values (r₁ es₁) (match W-ΔΣ:t
                              [(cons W ΔΣ) (on-t W ΔΣ)]
                              [#f (values ⊥R ∅)]))
    (define-values (r₂ es₂) (match W-ΔΣ:f
                              [(cons W ΔΣ) (on-f W ΔΣ)]
                              [#f (values ⊥R ∅)]))
    (values (m⊔ r₁ r₂) (∪ es₁ es₂)))

  (: blame-on-transparent? : Err → Boolean)
  (define (blame-on-transparent? err)
    (define violator : (Err → -l)
      (match-lambda
        [(Err:Raised _ ℓ) (ℓ-src ℓ)]
        [(Err:Undefined _ ℓ) (ℓ-src ℓ)]
        [(Err:Values _ _ _ ℓ) (ℓ-src ℓ)]
        [(Err:Arity _ _ ℓ) (ℓ-src ℓ)]
        [(Err:Varargs _ _ ℓ) (ℓ-src ℓ)]
        [(Err:Sealed _ ℓ) (ℓ-src ℓ)]
        [(Blm l+ _ _ _ _) l+]))
    (transparent-module? (violator err)))
  )

(define-compound-unit/infer exec@
  (import meta-functions^ static-info^ ast-pretty-print^
          sto^ cache^ val^ pretty-print^
          prover^ prims^)
  (export exec^ hv^ mon^ app^)
  (link gc@ app@ evl@ mon@ hv@ fix@))
