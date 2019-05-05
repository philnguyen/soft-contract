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
         "../utils/patterns.rkt"
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

  (define $ᵢₙ  : $ ⊥$)
  (define $ₒᵤₜ : $ ⊥$) ; TODO strange that set! below complains without ann
  (define errs : (℘ Err) ∅)
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
                    (λ () (evl-prog p))
                    (λ () (evl ⊥Σ p))))
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
      (set! errs ∅)
      (hash-clear! dependencies)
      (clear-live-set-cache!))
    
    (let loop ([iter : Natural 0])
      (when dump-iter?
        (printf "iter ~a: ~a in, ~a dirties ~n" iter (hash-count $ᵢₙ) (set-count dirties)))
      (set! dirties ∅eq)
      (run)
      (if (or (done? iter) (set-empty? dirties))
          (values (set-filter blame-on-transparent? errs) $ᵢₙ)
          (begin
            (set! $ᵢₙ $ₒᵤₜ)
            (set! $ₒᵤₜ (for/fold ([acc : $ $ₒᵤₜ]) ([k (in-set dirties)])
                         (hash-remove acc k)))
            (loop (+ 1 iter))))))

  (: ref-$! : $:Key (→ R) → R)
  (define (ref-$! key* comp)
    (define key (intern-$:Key key*))
    (match (hash-ref $ₒᵤₜ key #f)
      [(? values r)
       ;; Record all configurations whose result depend on cache entry
       (hash-update! dependencies key (λ ([ks : (℘ $:K)]) (∪ ks (dependants))) mk-∅eq)
       r]
      [#f
       (define r₀ (hash-ref $ᵢₙ key (λ () ⊥R)))
       (set! $ₒᵤₜ (hash-set $ₒᵤₜ key r₀))
       (define r (parameterize ([dependants (set-add (dependants) key)])
                   (comp)))
       (define r* (R⊔ r₀ r))
       ;; If new result differ from cache entry, mark all dependcies as dirty
       (unless (equal? r₀ r*)
         (set! $ₒᵤₜ (hash-set $ₒᵤₜ key r*))
         (match (hash-ref dependencies key #f)
           [(? values deps)
            (set! dirties (∪ dirties deps))
            (hash-remove! dependencies key)]
           [_ (void)]))
       r*]))

  (: err! ((U (℘ Err) Err) → Void))
  (define (err! er)
    (set! errs (if (set? er) (∪ errs er) (set-add errs er))))

  (: blm : -l ℓ ℓ W W → (℘ Blm))
  (define (blm l+ ℓ ℓₒ ctc val)
    (if (transparent-module? l+) {set (Blm l+ ℓ ℓₒ ctc val)} ∅))

  (: fold-ans (∀ (X) (X → R) (℘ X) → R))
  (define (fold-ans on-X Xs)
    (for/fold ([r : R ⊥R]) ([X (in-set Xs)])
      (R⊔ r (on-X X))))

  (: fold-ans/collapsing (∀ (X) (X → R) (℘ X) → R))
  (define (fold-ans/collapsing on-X Xs)
    (match (collapse-R (fold-ans on-X Xs))
      [(cons Ws ΔΣ) (R-of (collapse-W^ Ws) ΔΣ)]
      [#f ⊥R]))

  (: with-split-Σ : Σ V W (W ΔΣ → R) (W ΔΣ → R) → R)
  (define (with-split-Σ Σ P W on-t on-f)
    (define-values (W-ΔΣ:t W-ΔΣ:f) (check-plaus Σ P W))
    (define r₁ (match W-ΔΣ:t
                 [(cons W ΔΣ) (on-t W ΔΣ)]
                 [#f ⊥R]))
    (define r₂ (match W-ΔΣ:f
                 [(cons W ΔΣ) (on-f W ΔΣ)]
                 [#f ⊥R]))
    (R⊔ r₁ r₂))

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

  (: fix-return : Renamings Σ R → R)
  (define (fix-return rn Σ₀ r)
    (define Σₑᵣ ((inst make-parameter Σ) Σ₀)) ; HACK to reduce cluttering
    (define adjust-T (rename rn))
    (define (go-ΔΣ [ΔΣ₀ : ΔΣ])
      (match-define (cons ΔΞ₀ ΔΓ₀) ΔΣ₀)
      (cons ΔΞ₀ (go-ΔΓ ΔΓ₀)))
    (define (go-ΔΓ [ΔΓ₀ : ΔΓ])
      (for/fold ([acc : ΔΓ ⊤ΔΓ]) ([(T D) (in-hash ΔΓ₀)])
        (match (adjust-T T)
          [(? values T*)
           ;; If calle is wrapped in higher-order contract,
           ;; then `T` and `T*` are not the same values.
           ;; But we trust that if `ℰ[f] ⇓ V₁` and `ℰ[f ▷ C] ⇓ V₂`
           ;; then `V₁ ≃ V₂`, where `≃` is equality for all flat values
           (define D* (go-V^ (assert D set?)))
           (if (and (γ:lex? T*) (set-ormap Guarded? D*))
               acc
               (hash-set acc T* D*))]
          [_ acc])))
    (define (go-W [W : W]) (map go-V^ W))
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

  (: make-renamings : (U (Listof Symbol) -formals) W → Renamings)
  (define (make-renamings fml W)
    (define xs (if (-var? fml) (-var-init fml) fml))
    (define-values (W₀ Wᵣ) (if (and (-var? fml) (-var-rest fml))
                               (split-at W (length xs))
                               (values W #f)))
    (define m
      (for/hash : Renamings ([x (in-list xs)] [Vs (in-list W₀)])
        (values (γ:lex x)
                (and (not (assignable? x))
                     (match Vs
                       [{singleton-set (? T? T)} T]
                       [_ #f])))))
    (match fml
      [(-var _ (? values z)) (hash-set m (γ:lex z) #f)]
      [_ m]))

  (: rename : Renamings → (case->
                           [T → (Option T)]
                           [(U T -b) → (Option (U T -b))]))
  ;; Compute renaming in general.
  ;; `#f` means there's no correspinding name
  (define (rename rn)
    (: go-K : (K → (Option K)))
    (define (go-K K) (if (T? K) (go K) K))
    (: go (case-> [T → (Option T)]
                  [(U T -b) → (Option (U T -b))]))
    (define (go T₀)
      (if (hash-has-key? rn T₀)
          (hash-ref rn T₀)
          (match T₀
            [(T:@ o Ts)
             (match (go-K o)
               [(? values o*) (define Ts* (go* Ts))
                              (and Ts* (T:@ o* Ts*))]
               [#f #f])]
            [_ T₀])))
    (define go* : ((Listof (U T -b)) → (Option (Listof (U T -b))))
      (match-lambda
        ['() '()]
        [(cons T Ts) (match (go T)
                       [#f #f]
                       [(? values T*) (match (go* Ts)
                                        [#f #f]
                                        [(? values Ts*) (cons T* Ts*)])])]))
    go)
  )

(define-compound-unit/infer exec@
  (import meta-functions^ static-info^ ast-pretty-print^
          sto^ cache^ val^ pretty-print^
          prover^ prims^)
  (export exec^ hv^ mon^ app^)
  (link gc@ app@ evl@ mon@ hv@ fix@))
