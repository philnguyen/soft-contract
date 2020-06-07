#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/set
         racket/match
         "signatures.rkt")

(define-unit params@
  (import sto^ val^ pretty-print^)
  (export params^)

  (define -current-params ((inst make-parameter B) (hash)))

  (: current-parameters : → B)
  (define current-parameters -current-params)

  (: current-parameter ([α] [(→ V^)] . ->* . V^))
  (define (current-parameter α [default (λ () (error 'current-parameter "Nothing at ~a" α))])
    (hash-ref (current-parameters) α default))

  (: with-parameters (∀ (X) (Listof (Pairof V^ V^)) (→ X) → X))
  (define (with-parameters bindings exec) (with-params bindings (exec)))

  (: with-parameters-2 (∀ (X Y) (Listof (Pairof V^ V^)) (→ (Values X Y)) → (Values X Y)))
  (define (with-parameters-2 bindings exec) (with-params bindings (exec)))

  (: set-parameter : α V^ → Void)
  (define (set-parameter α V)
    (-current-params (hash-update (current-parameters) α (λ ([V₀ : V^]) (V⊔ V₀ V)) (λ () V))))

  (define-syntax-rule (with-params bnds body)
    (parameterize ([-current-params
                    (for*/fold ([params : B (-current-params)]) ([b (in-list bnds)]
                                                                 [p (in-set (car b))])
                      (match p
                        [(Param α) (hash-set params α (cdr b))]
                        [_ (error 'with-parameters "LHS ~a not supported" (show-V p))]))])
      body))
  )
