#lang typed/racket/base

(provide termination@)

(require racket/match
         (except-in racket/set for/set for/seteq for*/set for*/seteq)
         typed/racket/unit
         unreachable
         bnf
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit termination@
  (import prover^)
  (export termination^)

  (?Ch . ≜ . (Option Ch))

  (: update-call-record : M Clo W ℓ Φ^ Σ → (Option M))
  (define (update-call-record M₀ Vₕ Wₓ ℓ Φ^ Σ)
    (match (hash-ref M₀ Vₕ #f)
      [(Call-Record W₀ G₀)
       (define G (make-sc-graph W₀ Wₓ Φ^ Σ))
       (and (strict-progress? G)
            (let ([G* (concat-graph G₀ G)])
              (and (strict-progress? G*)
                   (hash-set M₀ Vₕ (Call-Record Wₓ G*)))))]
      [#f (hash-set M₀ Vₕ (Call-Record Wₓ (init-sc-graph (V-arity Vₕ))))]))

  (define/memo (init-sc-graph [a : (U Natural arity-at-least)]) : SCG
    (define n (match a
                [(arity-at-least n) (+ 1 n)]
                [(? integer? n) n]))
    (for/hash : SCG ([i (in-range n)])
      (values (cons i i) '↓)))

  (: make-sc-graph : W W Φ^ Σ → SCG)
  (define (make-sc-graph W₀ W₁ Φ^ Σ)
    (unless (= (length W₀) (length W₁))
      (error 'make-sc-graph "TODO: generalize construction of size-change graphs for argument lists of mismatched lengths ~a and ~a" (length W₀) (length W₁)))
    (for*/hash : SCG ([(V^₀ i₀) (in-indexed W₀)]
                      [(V^₁ i₁) (in-indexed W₁)]
                      [?↓ (in-value (cmp V^₀ V^₁ Φ^ Σ))] #:when ?↓)
      (values (cons i₀ i₁) ?↓)))

  (: cmp : V^ V^ Φ^ Σ → ?Ch)
  (define (cmp V^₀ V^₁ Φ^ Σ)
    (for*/fold ([↝ : ?Ch '↓])
               ([V₀ (in-set V^₀)]
                [V₁ (in-set V^₁)]
                #:break (not ↝))
      (Ch-worst (assert ↝) (cmp₁ V₀ V₁ Φ^ Σ))))

  (: cmp₁ : V V Φ^ Σ → ?Ch)
  (define (cmp₁ V₀ V₁ Φ^ Σ)
    #|FIXME|#
    #f)

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
  (define (strict-progress? G) (for/or ([d (in-hash-values G)]) (eq? d '↓))))
