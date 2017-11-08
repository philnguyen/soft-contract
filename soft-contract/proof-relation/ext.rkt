#lang typed/racket/base

(provide external-prover@)

(require racket/match
         racket/set
         racket/list
         racket/splicing
         (only-in z3/ffi toggle-warning-messages!)
         typed/racket/unit
         z3/smt
         bnf
         intern
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "../signatures.rkt")

;; TODO I should have used reader monad for z3/smt instead of this hack
(define-type (M T) (→ T))

(define-unit external-prover@
  (import static-info^ for-gc^ pretty-print^ path^ sto^)
  (export external-prover^)

  (: p∋V : -Γ -h (Listof -V) → -R)
  ;; TODO use `define/memo` once Typed Unit is fixed
  (define (p∋V Γ p Vs)
    #;(define (set-default-options!)
        (set-options! #:timeout 1000
                      #:mbqi? #t
                      #:macro-finder? #t
                      #:rlimit 4000000))

    (cond
      [(handled-pred? p)
       (define-values (do-base do-target) (translate Γ p Vs))
       (case (run (do do-base
                      (λ () (assert! (do-target)))
                      check-sat))
         [(unsat) '✗]
         [(sat unknown)
          (case (run (do do-base
                         (λ () (assert-not! (do-target)))
                         check-sat))
            [(unsat) '✓]
            [(sat unknown) '?])])]
      [else '?]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Translate
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: translate : -Γ Handled-Pred (Listof -V) → (Values (M Void) (M Z3-Ast)))
  (define (translate Γ p Vs)
    (error 'TODO))

  (define-type Handled-Pred (U '< '<= '> '>= '= 'equal? 'zero?))
  (define-predicate handled-pred? Handled-Pred)

  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; For-Translate
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ret (∀ (α) α → (M α)))
  (define (ret v) (λ () v))

  (: >>= (∀ (α β) (M α) (α → (M β)) → (M β)))
  (define ((a . >>= . mb)) ((mb (a))))

  (define-syntax do
    (syntax-rules (← ≔ :)
      [(_ m) m]
      [(_ [p : τ ← m₁] m ...) (m₁ . >>= . (λ ([x : τ])
                                            (match-define p x)
                                            (do m ...)))]
      [(_ [p ≔ e ] m ...) (match-let ([p e]) (do m ...))]
      [(_  m₁      m ...) (m₁ . >>= . (λ _ (do m ...)))]))

  (: run (∀ (α) (M α) → α))
  (define (run m)
    (with-new-context (m)))

  (define (assert-not! [ψ : Z3-Ast]) (assert! (not/s ψ)))

  (toggle-warning-messages! #f))
