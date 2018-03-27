#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit val@
  (import sto^)
  (export val^)

  (: C-flat? : V → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? V)
    (match V
      [(And/C flat? _ _) flat?]
      [(Or/C flat? _ _) flat?]
      [(? Not/C?) #t]
      [(? One-Of/C?) #t]
      [(St/C flat? _ _) flat?]
      [(or (? Vectof?) (? Vect/C?)) #f]
      [(Hash/C _ _) #f] ; TODO
      [(Set/C _) #f] ; TODO
      [(? Fn/C?) #f]
      [(or (? Clo?) (X/G (? Fn/C?) _ _) (? -prim?)) #t]
      [(? X/C?) #t]
      [(? ∀/C?) #f]
      [(? Seal/C?) #f]
      [V (error 'C-flat? "Unepxected: ~a" V)]))

  (: C^-flat? : V^ → Boolean)
  (define (C^-flat? C^)
    (for/and : Boolean ([C (in-set C^)]) (C-flat? C)))

  (:* with-negative-party with-positive-party : -l V → V)
  (define with-negative-party
    (match-lambda**
     [(l- (X/G C α (Ctx l+ _ lo ℓ))) (X/G C α (Ctx l+ l- lo ℓ))]
     [(_ V) V]))
  (define with-positive-party
    (match-lambda**
     [(l+ (X/G C α (Ctx _ l- lo ℓ))) (X/G C α (Ctx l+ l- lo ℓ))]
     [(_ V) V]))

  (: behavioral? : Σᵥ V → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? Σᵥ v)
    (define-set seen : α #:eq? #t #:as-mutable-hash? #t)

    (: check-α : α → Boolean)
    (define (check-α α)
      (cond [(seen-has? α) #f]
            [else
             (seen-add! α)
             (set-ormap check (Σᵥ@ Σᵥ α))]))

    (define check-αℓ : (αℓ → Boolean) (compose1 check-α αℓ-_0))

    (: check : V → Boolean)
    (define check
      (match-lambda
        [(St _ αs) (ormap check-α αs)]
        [(X/G _ G α) (or (Fn/C? G) (check-α α))]
        [(Vect αs) (ormap check-α αs)]
        [(Vect^ α _) (check-α α)]
        [(==> (-var doms domᵣ) rngs)
         (or (and (pair? rngs) (ormap check-αℓ rngs))
             (and domᵣ (check-αℓ domᵣ))
             (ormap check-αℓ doms))]
        [(? ==>i?) #t]
        [(Case-=> cases) (ormap check cases)]
        [(or (? Clo?) (? Case-Clo?)) #t]
        [_ #f]))

    (check v))

  (define guard-arity : (Fn/C → Arity)
    (match-lambda
      [(==> αs _) (shape αs)]
      [(==>i Doms _) (length Doms)]
      [(Case-=> cases) (normalize-arity (map guard-arity cases))]
      [(? ∀/C?)
       ;; TODO From observing behavior in Racket. But this maybe unsound for proof system
       (arity-at-least 0)]))

  (: blm-arity : ℓ -l Arity (Listof V^) → Blm)
  (define blm-arity
    (let ([arity->msg
           (match-lambda
             [(? integer? n)
              (format-symbol (case n
                               [(0 1) "~a value"]
                               [else "~a values"])
                             n)]
             [(arity-at-least n)
              (format-symbol "~a+ values" n)])])
      (λ (ℓ lo arity Vs)
        (Blm (strip-ℓ ℓ) lo (list (arity->msg arity)) Vs))))

  (: collapse-value-lists : W^ Natural → W)
  (define (collapse-value-lists W^ n)
    (define W-vec : (Vectorof V^) (make-vector n ⊥V))
    (for ([W (in-set W^)])
      (for ([V^ (in-list W)] [i (in-naturals)])
        (vector-set! W-vec i (V⊔ (vector-ref W-vec i) V^))))
    (vector->list W-vec))

  (: V⊔ : V^ V^ → V^)
  (define (V⊔ V^₁ V^₂)
    (for/fold ([V^ : V^ V^₁]) ([V (in-set V^₂)])
      (V⊔₁ V^ V)))

  (: V⊔₁ : V^ V → V^)
  (define (V⊔₁ V^ V) (set-add V^ V))

  (define ⊥V : V^ ∅)

  #;(: estimate-list-lengths : -σ -δσ -V → (℘ (U #f Arity)))
  ;; Estimate possible list lengths from the object language's abstract list
  #;(define (estimate-list-lengths σ δσ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define maybe-non-proper-list? : Boolean #f)

    (: arity-inc : Arity → Arity)
    (define arity-inc
      (match-lambda
        [(? exact-integer? n) (+ 1 n)]
        [(arity-at-least n) (arity-at-least (+ 1 n))]))
    
    (: go! : -V → (℘ Arity))
    (define go!
      (match-lambda
        [(-Cons _ αₜ)
         (cond [(seen-has? αₜ) {set (arity-at-least 0)}]
               [else (seen-add! αₜ)
                     (for/union : (℘ Arity) ([V* (in-set (σ@ σ δσ αₜ))])
                       (map/set arity-inc (go! V*)))])]
        [(-b '()) {set 0}]
        [(-● ps) #:when (∋ ps 'list?) {set (arity-at-least 0)}]
        [_ (set! maybe-non-proper-list? #t)
           ∅]))
    (define res
      (match (normalize-arity (set->list (go! V)))
        [(? list? l) (list->set l)]
        [a {set a}]))
      (if maybe-non-proper-list? (set-add res #f) res))

  (: K+ : F Ξ:co → Ξ:co)
  (define (K+ F Ξ)
    (match-define (Ξ:co K α H) Ξ)
    (Ξ:co (cons F K) α H))
  )
