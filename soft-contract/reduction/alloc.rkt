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
          val^ env^ evl^
          prover^ approx^)
  (export alloc^)

  (: mutable? : α → Boolean)
  (define (mutable? α)
    (match (inspect-α α)
      [(-α:x x _) (assignable? x)]
      [(-α:fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α:idx?) #t]
      [_ #f])) 

  (splicing-local
      ((: mk-list-S : W → (Option S))
       (define (mk-list-S W)
         (and (andmap S? W)
              (foldr (λ ([S : S] [acc : S]) (S:@ -cons (list S acc))) -null W)))

       (: er->ee : Φ^ (-var α) W Boolean (℘ α) → Φ^)
       (define (er->ee Φ^ₑᵣ fmls arg-list looped? scope)
         
         (define args : (-var T^)
           (if (-var-rest fmls)
               (let-values ([(Wᵢ Wᵣ) (split-at arg-list (length (-var-init fmls)))])
                 (-var Wᵢ (mk-list-S Wᵣ)))
               (-var arg-list #f)))

         (define ext-$ : ($ → $)
           (let-values ([(αs Ss)
                         (for/lists ([αs : (Listof α)] [Ss : (Listof S)])
                                    ([α : α (in-var fmls)] [T (in-var args)] #:unless (mutable? α))
                           (define S (if (and (S? T) (not looped?) (in-scope? T scope))
                                         T
                                         (S:α α)))
                           (values α S))])
             (λ ($₀) (foldl (λ ([α : α] [S : S] [$ : $]) (hash-set $ α S)) $₀ αs Ss))))

         (define ext-Ψ : (Ψ Ψ → Ψ)
           (let* ([mappings
                   (var-fold (λ ([α : α] [T : T^] [m : (Immutable-HashTable S S:α)])
                               (if (S? T) (hash-set m T (S:α α)) m))
                             ((inst hash S S:α)) fmls args)]
                  [er? (λ ([S : S]) (hash-has-key? mappings S))]
                  [subst₁
                   (λ ([Sₑᵣ : S]) : (Option S)
                      (cond [(hash-ref mappings Sₑᵣ #f) => values]
                            [(in-scope? Sₑᵣ scope) Sₑᵣ]
                            [else #f]))]
                  [subst
                   (λ ([Ss : (Listof S)]) : (Option (Listof S))
                     (foldr (λ ([Sᵢ : S] [acc : (Option (Listof S))])
                              (and acc (let ([Sᵢ* (subst₁ Sᵢ)]) (and Sᵢ* (cons Sᵢ* acc)))))
                            '()
                            Ss))])
             (λ (Ψₑₑ Ψₑᵣ)
               (for*/fold ([Ψ : Ψ Ψₑₑ])
                          ([(argsₑᵣ Ps) (in-hash Ψₑᵣ)]
                           #:when (ormap er? argsₑᵣ)
                           [?argsₑₑ (in-value (subst argsₑᵣ))]
                           #:when ?argsₑₑ)
                 (Ψ+ Ψ Ps ?argsₑₑ)))))

         (for/set : Φ^ ([Φₑᵣ (in-set Φ^ₑᵣ)])
           (match-define (Φ $ₑᵣ Ψₑᵣ) Φₑᵣ)
           (Φ (ext-$ ($↓ $ₑᵣ scope)) (ext-Ψ (Ψ↓ Ψₑᵣ scope) Ψₑᵣ))))

       (: alloc! : Σ Φ^ (-var α) W → Void)
       (define (alloc! Σ Φ^ αs W)
         (match-define (-var αs₀ ?αᵣ) αs)
         (for ([α (in-list αs₀)] [T (in-list W)])
           (⊔T! Σ Φ^ α T))
         (when ?αᵣ
           (match-define (-α:x x H) (inspect-α ?αᵣ))
           (⊔T! Σ Φ^ ?αᵣ (alloc-rest! x (drop W (length αs₀)) H Φ^ Σ))))

       (: ext-env : Ρ -formals (-var α) → Ρ)
       (define (ext-env Ρ₀ xs αs)
         (define f : (Symbol α Ρ → Ρ) (λ (x α Ρ) (Ρ+ Ρ x α)))
         (var-fold f Ρ₀ xs αs)))
    
    (: bind-args! : Φ^ Ρ -formals W H Σ → (Values Φ^ Ρ))
    (define (bind-args! Φ^ Ρ fmls W H Σ)
      (define fmls:addr (var-map (λ ([x : Symbol]) (mk-α (-α:x x H))) fmls))
      (define scope (set-subtract (hash-ref binders H) (var->set fmls:addr #:eq? #t)))
      (alloc! Σ Φ^ fmls:addr W)
      (values (er->ee Φ^ fmls:addr W (looped? H) scope) (ext-env Ρ fmls fmls:addr))))

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
