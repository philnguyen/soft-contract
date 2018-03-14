#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         typed/racket/unit
         set-extras
         intern
         bnf
         traces/typed
         unreachable
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "signatures.rkt"
         "reduction/signatures.rkt"
         )

;; Compacting each store to its version to display
(Ξ* . ::= . (Ξ* Ξ Σᵥ Σₖ Σₐ))

(define-unit verifier@
  (import static-info^ step^ compile^ parser^)
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))

  (: run : Runnable → (Values (℘ Blm) Σ))
  (define (run x)
    (with-initialized-static-info
      (↝* (comp x))))

  (: havoc : (Listof Path-String) → (Values (℘ Blm) Σ))
  (define (havoc ps) ???
    #;(with-initialized-static-info
      (define ms (parse-files ps))
      (↝* (↓ₚ (-prog ms (gen-havoc-expr ms))))))

  (: havoc/profile ([(Listof Path-String)]
                    [#:delay Positive-Real]
                    . ->* . (Values (℘ Blm) Σ)))
  (define (havoc/profile ps #:delay [delay 0.05])
    (let ([ans : (℘ Blm) ∅]
          [Σ : (Option Σ) #f])
      ((inst profile-thunk Void)
       (λ () (set!-values (ans Σ) (havoc ps))) #:delay delay)
      (values ans (assert Σ))))

  (: havoc-last : (Listof Path-String) → (Values (℘ Blm) Σ))
  (define (havoc-last ps) ???
    #;(with-initialized-static-info
      (define ms (parse-files ps))
      (run (↓ₚ ms (gen-havoc-expr (list (last ms)))))))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Visualization
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

  (: viz : Runnable → Σ)
  (define (viz x)
    (define-values (Ξ₀ Σ₀) (inj (comp x)))

    (define (Ξ->Ξ* [Ξ : Ξ]) : Ξ*
      ;; depending on mutable state Σ₀
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (Ξ* Ξ Σᵥ Σₖ Σₐ))

    (define Ξ*->Ξ : (Ξ* → Ξ)
      (match-lambda [(Ξ* Ξ _ _ _) Ξ]))
    
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (λ (Ξ*) (map/set Ξ->Ξ* (↝ (Ξ*->Ξ Ξ*) Σ₀))))
    
    (function-traces ↝₁ (Ξ->Ξ* Ξ₀))
    Σ₀)

  (: comp : Runnable → ⟦E⟧)
  (define (comp x)
    (cond [(-prog? x) (↓ₚ x)]
          [(list? x) (↓ₚ (-prog (parse-files x)))]
          [else (↓ₑ 'top-level x)]))
  )

