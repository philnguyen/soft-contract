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
          cache^ val^
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
        [(? values n) (λ () (> iter n))]
        [#f (λ () #f)]))
    
    (let loop ()
      (when dump-iter?
        (printf "iter: ~a~n" iter))
      (set! iter (+ 1 iter))
      (set! $ᵢₙ $ₒᵤₜ)
      (set! $ₒᵤₜ (⊥$))
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

  (: err (Err → (Values R (℘ Err))))
  (define (err er) (values ⊥R {set er}))

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
