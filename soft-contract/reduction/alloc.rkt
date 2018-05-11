#lang typed/racket/base

(provide alloc@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function const)
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/list
         racket/match
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         bnf
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit alloc@
  (import static-info^ meta-functions^
          val^ env^ sto^ evl^
          prover^)
  (export alloc^)

  (: mutable? : α → Boolean)
  (define (mutable? α)
    (match (inspect-α α)
      [(-α:x x _) (assignable? x)]
      [(-α:fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α:idx?) #t]
      [_ #f]))

  (: bind-args! : Φ^ Ρ -formals W H Σ → (Values Φ^ Ρ))
  (define (bind-args! Φ^₀ Ρ₀ fmls W H Σ)
    (match-define (-var xs x) fmls)
    (define-values (Φ^* Ρ*) (bind-inits! Φ^₀ Ρ₀ xs W H Σ))
    (if x
        (bind-rest! Φ^* Ρ* x (drop W (length xs)) H Σ)
        (values Φ^* Ρ*)))

  (splicing-local
      ((: bind! : Σ Φ^ Ρ Symbol H T^ → (Values Φ^ Ρ))
       (define (bind! Σ Φ^ Ρ x H T)
         (define α (mk-α (-α:x x H)))
         (define V^ (T->V Σ Φ^ T))
         (⊔ᵥ! Σ α V^)
         (define Φ^*
           (if (mutable? α)
               Φ^
               (let ([S (if (and (S? T)
                                 (not (looped? H))
                                 (T . in-scope? . (hash-ref binders H)))
                            T
                            (S:α α))])
                 ($+ Φ^ α S))))
         (values Φ^* (Ρ+ Ρ x α))))
    
    (: bind-inits! : Φ^ Ρ (Listof Symbol) W H Σ → (Values Φ^ Ρ))
    (define (bind-inits! Φ^₀ Ρ₀ xs W H Σ)
      (for/fold ([Φ^ : Φ^ Φ^₀] [Ρ : Ρ Ρ₀])
                ([x (in-list xs)] [V (in-list W)])
        (bind! Σ Φ^ Ρ x H V)))

    (: bind-rest! ([Φ^ Ρ Symbol W H Σ] [#:end T^] . ->* . (Values Φ^ Ρ)))
    (define (bind-rest! Φ^ Ρ x W H Σ #:end [Vₙ -null])
      (bind! Σ Φ^ Ρ x H (alloc-rest! x W H Φ^ Σ #:end Vₙ))))

  (: alloc-rest! ([(U Symbol ℓ) W H Φ^ Σ] [#:end T^] . ->* . T^))
  (define (alloc-rest! x Wₓ H Φ^ Σ #:end [Tₙ {set -null}])
    (let go! ([W : W Wₓ] [i : Natural 0])
      (match W
        [(cons Vᵢ W*)
         (define αₕ (mk-α (-α:var:car x H i)))
         (define αₜ (mk-α (-α:var:cdr x H i)))
         (⊔T! Σ Φ^ αₕ Vᵢ)
         (⊔T! Σ Φ^ αₜ (go! W* (+ 1 i)))
         {set (Cons αₕ αₜ)}]
        [_ Tₙ])))

  (: H+ : H ℓ (Option Clo) (U 'app 'mon) → H)
  (define (H+ H₀ src fn type)
    (define-values (H* looped?) (-H+ (inspect-H H₀) src fn type))
    (define H₁ (mk-H H*))
    (when looped?
      (hash-set! looped-ctxs H₁ #t))
    (unless (hash-has-key? binders H₁)
      (define αs
        (cond [fn (for/seteq : (℘ α) ([x (in-set (formals->names (Clo-_0 fn)))])
                    (mk-α (-α:x x H₁)))]
              [else ∅eq]))
      (hash-set! binders H₁ (∪ αs (hash-ref binders H₀))))
    H₁)

  (: -H+ : -H ℓ (Option Clo) (U 'app 'mon) → (Values -H Boolean))
  (define (-H+ H src fn type)
    (match-define (-H:edges edges) H)
    (define tgt (and fn (Clo-_1 fn)))
    (case type
      [(app)
       (define match? : (Edge → Boolean)
         (match-lambda [(Edge _ tgt*) (equal? tgt* tgt)]))
       (define ?edges* (memf match? edges))
       (cond [?edges* (values (-H:edges ?edges*) #t)]
             [else (values (-H:edges (cons (Edge src tgt) edges)) #f)])]
      [(mon) ???]))

  (define (looped? [H : H]) (hash-has-key? looped-ctxs H))


  (define H₀ (mk-H (-H:edges '())))

  (define looped-ctxs : (Mutable-HashTable H #t) (make-hasheq))
  (define binders : (Mutable-HashTable H (℘ α)) (make-hasheq (list (cons H₀ ∅eq))))
  )

(define-substructs -H
  [-H:edges (Listof Edge)])

(Edge . ::= . (Edge [src : ℓ] [tgt : (Option ⟦E⟧)]))
