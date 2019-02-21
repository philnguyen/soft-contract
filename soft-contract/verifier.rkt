#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         racket/set
         typed/racket/unit
         set-extras
         intern
         bnf
         unreachable
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "signatures.rkt"
         "reduction/signatures.rkt"
         )

(define-interner Ver-V Σᵥ)
(define-interner Ver-K Σₖ)
(define-interner Ver-A Σₐ)
(Ξ* . ::= . (Ξ* Ξ Σᵥ Ver-K R^))

(define-unit verifier@
  (import parser^
          meta-functions^
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

  (: optimize : -module (℘ Blm) → -module)
  (define (optimize m blms)
    ;; Collect potential sites and contract sources of violation
    (define-values (origins sites)
      (for/fold ([origins : (℘ ℓ) ∅eq] [sites : (℘ ℓ) ∅eq])
                ([blm (in-set blms)])
        (values (set-add origins (Blm-origin blm))
                (set-add sites   (Blm-site blm)))))
    ;; Split out optimized module
    (optimize-uses sites (optimize-contracts origins m)))

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

