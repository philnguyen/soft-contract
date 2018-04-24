#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         racket/set
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
(Ξ* . ::= . (Ξ* ⟨Ξ⟩ Σᵥ ⟨Σₖ⟩ ⟨Σₐ⟩))
(define-interner ⟨αₖ⟩ αₖ
  #:intern-function-name mk-αₖ
  #:unintern-function-name inspect-αₖ)
(⟨Ξ⟩ . ::= . (⟨Ξ:co⟩ [kon : ⟨K⟩] [hist : M] [ctx : H]) Blm)
(⟨K⟩ . ::= . (⟨K⟩ (Listof F) ⟨αₖ⟩))
(⟨Σₖ⟩ . ≜ . (Immutable-HashTable ⟨αₖ⟩ (Setof ⟨Ξ:co⟩)))
(⟨Σₐ⟩ . ≜ . (Immutable-HashTable ⟨Ξ:co⟩ R^))

(: -⟨Ξ⟩ (case-> [Ξ:co → ⟨Ξ:co⟩]
                [Blm → Blm]
                [Ξ → ⟨Ξ⟩]))
(define -⟨Ξ⟩
  (match-lambda
    [(Ξ:co (K Fs α) M H) (⟨Ξ:co⟩ (⟨K⟩ Fs (mk-αₖ α)) M H)]
    [(? Blm? b) b]))

(: -⟨Σₖ⟩ : Σₖ → ⟨Σₖ⟩)
(define (-⟨Σₖ⟩ Σₖ)
  (for/hasheq : ⟨Σₖ⟩ ([(α Ξs) (in-hash Σₖ)])
    (values (mk-αₖ α) (map/set -⟨Ξ⟩ Ξs))))

(: -⟨Σₐ⟩ : Σₐ → ⟨Σₐ⟩)
(define (-⟨Σₐ⟩ Σₐ)
  (for/hash : ⟨Σₐ⟩ ([(Ξ Rs) (in-hash Σₐ)])
    (values (-⟨Ξ⟩ Ξ) Rs)))

(: -Ξ (case-> [⟨Ξ:co⟩ → Ξ:co]
              [Blm → Blm]
              [⟨Ξ⟩ → Ξ]))
(define -Ξ
  (match-lambda
    [(⟨Ξ:co⟩ (⟨K⟩ Fs α) M H) (Ξ:co (K Fs (inspect-αₖ α)) M H)]
    [(? Blm? b) b]))

(define-unit verifier@
  (import parser^
          static-info^
          sto^
          step^ compile^ (prefix hv: havoc^))
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))

  (: run : Runnable → (Values (℘ Blm) Σ))
  (define (run x)
    (with-initialized-static-info
      (↝* (comp x))))

  (: havoc : (Listof Path-String) → (Values (℘ Blm) Σ))
  (define (havoc ps)
    (with-initialized-static-info
      (↝* (comp ps #:havoc? #t))))

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
  (define (havoc-last ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (define hv (-module 'havoc (list (hv:gen-havoc-expr (list (last ms))))))
      (↝* (↓ₚ (-prog `(,@ms ,hv))))))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Visualization
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

  (: viz : Runnable → Σ)
  (define (viz x)
    (define-values (Ξ₀ Σ₀) (inj (comp x #:havoc? #t)))

    (define (Ξ->Ξ* [Ξ : Ξ]) : Ξ*
      ;; depending on mutable state Σ₀
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (Ξ* (-⟨Ξ⟩ Ξ) Σᵥ (-⟨Σₖ⟩ Σₖ) (-⟨Σₐ⟩ Σₐ)))

    (define Ξ*->Ξ : (Ξ* → Ξ)
      (match-lambda [(Ξ* Ξ _ _ _) (-Ξ Ξ)]))
    
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (λ (Ξ*) (map/set Ξ->Ξ* (↝ (Ξ*->Ξ Ξ*) Σ₀))))
    
    (function-traces ↝₁ (Ξ->Ξ* Ξ₀))
    Σ₀)

  (: viz-call-graph : Runnable → Void)
  (define (viz-call-graph x)
    (match-define-values (_ (Σ _ Σₖ _)) (run x))
    (cond
      [(hash-empty? Σₖ) (printf "Empty call graph~n")]
      [else
       (define CG (construct-call-graph Σₖ))
       (define entry
         (assert (for/or : (Option αₖ) ([αₖ (in-hash-keys CG)]
                                        #:when (set-empty? (Σₖ@ Σₖ αₖ)))
                   αₖ)))
       (hash-traces CG entry)]))

  (: comp ([Runnable] [#:havoc? Boolean] . ->* . ⟦E⟧))
  (define (comp x #:havoc? [havoc? #f])
    (define (maybe-with-hv [ms : (Listof -module)])
      (if havoc?
          `(,@ms ,(-module 'havoc (list (hv:gen-havoc-expr ms))))
          ms))
    (cond [(-prog? x) (↓ₚ (-prog (maybe-with-hv (-prog-_0 x))))]
          [(list? x) (↓ₚ (-prog (maybe-with-hv (parse-files x))))]
          [else (↓ₑ 'top-level x)]))
  )

