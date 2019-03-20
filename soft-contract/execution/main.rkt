#lang typed/racket/base

(provide exec@)

(require racket/set
         racket/list
         racket/match
         racket/vector
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
          evl^ gc^
          prover^)
  (export exec^)

  (define ⊥A : (Pairof R (℘ Err)) (cons ⊥R ∅))
  (define $ᵢₙ  : $ ⊥$)
  (define $ₒᵤₜ : $ ⊥$) ; TODO strange that set! below complains without ann
  (define db:iter? ((inst make-parameter Boolean) #f))
  (define db:max-steps ((inst make-parameter (Option Index)) #f))
  (define db:depth ((inst make-parameter Natural) 0))
  (define current-module ((inst make-parameter -l) 'scv))

  ;;; For incremental
  ;; Configurations that depend on result of current computation
  (define dependants ((inst make-parameter (℘ $:K)) ∅eq))
  ;; Map each configuration to the ones whose result depend on it
  (define dependencies : (Mutable-HashTable $:K (℘ $:K)) (make-hasheq))
  ;; Configurations whose entries in `$ₒᵤₜ` are invalidated
  (define dirties : (℘ $:K) ∅eq)

  (: exec : (U -prog E) → (Values (℘ Err) $))
  (define (exec p)
    (define run (if (-prog? p)
                    (λ () (let-values ([(_ es) (evl-prog p)]) es))
                    (λ () (let-values ([(_ es) (evl ⊥Σ p)]) es))))
    (define dump-iter? (db:iter?)) 
    (define iter : Natural 0)
    (define done? : (Natural → Boolean)
      (match (db:max-steps)
        [(? values n) (λ (iter) (>= iter n))]
        [#f (λ (_) #f)]))

    ;; Make sure global states are properly reset from possibly previously
    ;; verifying other programs in the same process
    (begin
      (set! $ₒᵤₜ ⊥$)
      (set! $ᵢₙ $ₒᵤₜ)
      (hash-clear! dependencies)
      (clear-live-set-cache!))
    
    (let loop ([iter : Natural 0])
      (when dump-iter?
        (printf "iter ~a: ~a in, ~a dirties ~n" iter (hash-count $ᵢₙ) (set-count dirties)))
      (set! dirties ∅eq)
      (define es (run))
      (if (or (done? iter) (set-empty? dirties))
          (values (set-filter blame-on-transparent? es) $ᵢₙ)
          (begin
            (set! $ᵢₙ $ₒᵤₜ)
            (set! $ₒᵤₜ (for/fold ([acc : $ $ₒᵤₜ]) ([k (in-set dirties)])
                         (hash-remove acc k)))
            (loop (+ 1 iter))))))

  (: ref-$! : $:K (→ (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (ref-$! key comp)
    (match (hash-ref $ₒᵤₜ key #f)
      [(cons r es)
       ;; Record all configurations whose result depend on cache entry
       (hash-update! dependencies key (λ ([ks : (℘ $:K)]) (∪ ks (dependants))) mk-∅eq)
       (values r es)]
      [#f
       (match-define (and res₀ (cons r₀ es₀)) (hash-ref $ᵢₙ key (λ () ⊥A)))
       (set! $ₒᵤₜ (hash-set $ₒᵤₜ key res₀))
       (define-values (r es) (parameterize ([dependants (set-add (dependants) key)])
                               (comp)))
       (define r* (R⊔ r₀ r))
       (define es* (∪ es₀ es))
       ;; If new result differ from cache entry, mark all dependcies as dirty
       (unless (and (equal? r₀ r*) (equal? es₀ es*))
         (set! $ₒᵤₜ (hash-set $ₒᵤₜ key (cons r* es*)))
         (match (hash-ref dependencies key #f)
           [(? values deps)
            (set! dirties (∪ dirties deps))
            (hash-remove! dependencies key)]
           [_ (void)]))
       (values r* es*)]))

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
        (values α* (cons (go-S (car r))
                         ;; if `α` is new allocation within callee and
                         ;; `α*` is existing address, store-delta entry for `α*`
                         ;; should always be refinement,
                         ;; so should not increase cardinality
                         (if (hash-has-key? rn α) 0 (cdr r))))))
    (define (go-W [W : W]) (map go-V^ W))
    (define (go-S [S : S])
      (if (vector? S) (vector-map go-V^ S) (go-V^ S)))
    (define (go-V^ [V^ : V^])
      (match-define (cons Vs₀ Vs*) (set-map V^ go-V))
      (foldl V⊔ Vs₀ Vs*))
    (define (go-V [V : V]) (if (T? V) (go-T V) {set V}))
    (define (go-T [T : T]) (cond [(adjust-T T) => set]
                                 [else (unpack T (Σₑᵣ))]))

    (for/fold ([acc : R ⊥R]) ([(Wᵢ ΔΣsᵢ) (in-hash r)])
      (define ΔΣᵢ (collapse-ΔΣs ΔΣsᵢ))
      (parameterize ([Σₑᵣ (⧺ Σ₀ ΔΣᵢ)])
        (define W* (go-W Wᵢ))
        (define ΔΣ* (go-ΔΣ ΔΣᵢ))
        (hash-set acc W*
                  (match (hash-ref acc W* #f)
                    [(? values ΔΣs₀) {set (collapse-ΔΣs (set-add ΔΣs₀ ΔΣ*))}]
                    [#f {set ΔΣ*}])))))

  (: fold-ans (∀ (X) (X → (Values R (℘ Err))) (℘ X) → (Values R (℘ Err))))
  (define (fold-ans on-X Xs)
    (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) ([X (in-set Xs)])
      (define-values (r* es*) (on-X X))
      (values (R⊔ r r*) (∪ es es*))))

  (: fold-ans/collapsing (∀ (X) (X → (Values R (℘ Err))) (℘ X) → (Values R (℘ Err))))
  (define (fold-ans/collapsing on-X Xs)
    (define-values (r es) (fold-ans on-X Xs))
    (values (match (collapse-R r)
              [(cons Ws ΔΣ) (R-of (collapse-W^ Ws) ΔΣ)]
              [#f ⊥R])
            es))

  (: with-split-Σ : Σ V W (W ΔΣ → (Values R (℘ Err))) (W ΔΣ → (Values R (℘ Err))) → (Values R (℘ Err)))
  (define (with-split-Σ Σ P W on-t on-f)
    (define-values (W-ΔΣ:t W-ΔΣ:f) (check-plaus Σ P W))
    (define-values (r₁ es₁) (match W-ΔΣ:t
                              [(cons W ΔΣ) (on-t W ΔΣ)]
                              [#f (values ⊥R ∅)]))
    (define-values (r₂ es₂) (match W-ΔΣ:f
                              [(cons W ΔΣ) (on-f W ΔΣ)]
                              [#f (values ⊥R ∅)]))
    (values (R⊔ r₁ r₂) (∪ es₁ es₂)))

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
