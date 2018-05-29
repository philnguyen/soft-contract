#lang typed/racket/base

(provide termination@)

(require racket/match
         (except-in racket/set for/set for/seteq for*/set for*/seteq)
         typed/racket/unit
         typed-racket-hacks
         unreachable
         bnf
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit termination@
  (import static-info^
          val^
          prover^)
  (export termination^)

  (?Ch . ≜ . (Option Ch))

  (: update-call-record : H M Clo W ℓ Φ^ Σ → (Option M))
  (define (update-call-record H M₀ Vₕ Wₓ ℓ Φ^ Σ)
    (match (hash-ref M₀ Vₕ #f)
      [(? values G₀)
       (when (-var-rest (Clo-_0 Vₕ))
         (error 'update-call-record "TODO: handle rest args ~a" (-var-rest (Clo-_0 Vₕ))))
       (define G
         (let ([W₀ (for/list : (Listof S:α) ([x (in-list (-var-init (Clo-_0 Vₕ)))])
                     (S:α (mk-α (-α:x x H))))])
           (make-sc-graph W₀ Wₓ Φ^ Σ)))
       (and (strict-progress? G)
            (let ([G* (concat-graph G₀ G)])
              (and (strict-progress? G*)
                   (hash-set M₀ Vₕ G*))))]
      [#f (hash-set M₀ Vₕ (init-sc-graph (T-arity Vₕ)))]))

  (define/memo (init-sc-graph [a : (U Natural arity-at-least)]) : SCG
    (define n (match a
                [(arity-at-least n) (+ 1 n)]
                [(? integer? n) n]))
    (for/hash : SCG ([i (in-range n)])
      (values (cons i i) '↓)))

  (: make-sc-graph : (Listof S:α) W Φ^ Σ → SCG)
  (define (make-sc-graph W₀ W₁ Φ^ Σ)
    (unless (= (length W₀) (length W₁))
      (error 'make-sc-graph "TODO: generalize construction of size-change graphs for argument lists of mismatched lengths ~a and ~a" (length W₀) (length W₁)))
    (for*/hash : SCG ([(T^₀ i₀) (in-indexed W₀)]
                      [(T^₁ i₁) (in-indexed W₁)]
                      [?↓ (in-value (cmp T^₀ T^₁ Φ^ Σ))] #:when ?↓)
      (values (cons i₀ i₁) ?↓)))

  (: cmp : T^ T^ Φ^ Σ → ?Ch)
  (define (cmp T^₀ T^₁ Φ^ Σ)
    (cond [(defly? (λ () (partition-results Σ (R (list T^₀ T^₁) Φ^) 'equal?))) '↧]
          [(check-≺ Σ Φ^ T^₁ T^₀) '↓]
          [else #f]))

  (: concat-graph : SCG SCG → SCG)
  (define (concat-graph G₁ G₂)
    (for*/fold ([G* : SCG (hash)])
               ([(edge₁ ↝₁) (in-hash G₁)]
                [i (in-value (cdr edge₁))]
                [(edge₂ ↝₂) (in-hash G₂)]
                #:when (eq? i (car edge₂)))
      (hash-update G* (cons (car edge₁) (cdr edge₂))
                   (λ ([↝₀ : Ch]) (Ch-best ↝₀ ↝₁ ↝₂))
                   (λ () '↧))))

  (define Ch-best : (Ch * → Ch)
    (λ chs (if (memq '↓ chs) '↓ '↧)))
  
  (define Ch-worst : (Ch ?Ch → ?Ch)
    (match-lambda**
     [(_  #f) #f]
     [('↧ _ ) '↧]
     [(_  '↧) '↧]
     [(_  _ ) '↓]))

  (: strict-progress? : SCG → Boolean)
  (define (strict-progress? G) (for/or ([d (in-hash-values G)]) (eq? d '↓)))

  (: check-≺ : Σ Φ^ T^ T^ → Boolean)
  (define (check-≺ Σ Φ^ T^₀ T^₁)
    (: must-be? : P T^ * → Boolean)
    (define (must-be? P . T^s) (defly? (λ () (partition-results Σ (R T^s Φ^) P))))
    (or (T^₀ . sub-value? . T^₁)
        (and (must-be? 'integer? T^₀)
             (must-be? 'integer? T^₁)
             (must-be? '<= -zero T^₀)
             (must-be? '< T^₀ T^₁))))

  (: sub-value? : T^ T^ → Boolean)
  (define (x . sub-value? . y)
    (define sub-ac? : (S → Boolean)
      (match-lambda [(-st-ac 𝒾 i) (not (struct-mutable? 𝒾 i))]
                    [_ #f]))
    
    (match* (x y)
      [((S:@ (? sub-ac?) (list x*)) (? S? y))
       (let loop ([x : S x*])
         (match x
           [(== y) #t]
           [(S:@ (? sub-ac?) (list x*)) (loop x*)]
           [_ #f]))]
      [(_ _) #f]))

  (: defly? : (→ (Values R^ R^ R^)) → Boolean)
  (define (defly? e)
    (define-values (_ R₂ R₃) (e))
    (and (set-empty? R₂) (set-empty? R₃)))
  )
